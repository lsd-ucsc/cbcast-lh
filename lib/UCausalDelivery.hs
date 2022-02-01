{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}
-- {-# LANGUAGE NoFieldSelectors #-}
{-# LANGUAGE NamedFieldPuns #-}
module UCausalDelivery where

import Language.Haskell.Liquid.ProofCombinators
import Redefined.Fin (fin)
import Redefined.Ord (ordMax)
import Redefined.Proof (proofConst)

import SystemModel
import Properties ()

-- * Causal Delivery MPA



-- ** VC sizing

-- How to compute VC sizes in refinements:
--
-- v:VC     len v
-- mm:VCMM  len (vcmmSent mm)
-- m:M r    len (mVC m)
-- p:P r    len (pVC p)

{-@ type VCasM M = VCsized {len (mVC M)} @-}

{-@ type VCMMsized N = {mm:VCMM | len (vcmmSent mm) == N} @-}
{-@ type VCMMasM M = VCMMsized {len (mVC M)} @-}

{-@
type M r = Message VCMM r @-} -- QQQ: Why is this required? Ditto below, I guess
type M r = Message VCMM r
{-@ type Msized r N = {m:M r | len (mVC m) == N} @-}
{-@ type MasV r V = Msized r {len V} @-}
{-@ type MasM r M = Msized r {len (mVC M)} @-}
{-@ type MasP r P = Msized r {len (pVC P)} @-}

type H r = ProcessHistory VCMM r
{-@ type Hsized r N = ProcessHistory {mm:VCMM | len (vcmmSent mm) == N} r @-}

type DQ r = [M r]
{-@ type DQsized r N = [Msized r {N}] @-}
{-@ type DQasV r V = DQsized r {len V} @-}
{-@ type DQasM r M = DQsized r {len (mVC M)} @-}

{-@
data P r = P {pid::PID, pVC::VC, dq::DQsized r {len pVC}, hist::Hsized r {len pVC}} @-}
data P r = P {pid::PID, pVC::VC, dq::DQ r, hist::H r}
{-@ type Psized r N = {p:P r | len (pVC p) == N} @-}
{-@ type PasP r P = Psized r {len (pVC P)} @-}
{-@ type PasM r M = Psized r {len (mVC M)} @-}

-- QQQ: Do we want to push these convenence aliases into the system model? Is
-- the definition of PLCD hard to read?

-- | When putting events into process history it's necessary to specify the vc
-- size in the type of the metadata.
{-@
coerce :: m:Message VCMM r -> Message (VCMMasM {m}) r @-}
coerce :: Message VCMM r -> Message VCMM r
coerce (Message a b) = Message a b
{-@ reflect coerce @-}



-- ** Message order

{-@
(===>) :: m:M r -> MasM r {m} -> Bool @-}
(===>) :: M r -> M r -> Bool
a ===> b = mVC a `vcLess` mVC b
{-@ reflect ===> @-}

{-@
(||||) :: m:M r -> MasM r {m} -> Bool @-}
(||||) :: M r -> M r -> Bool
a |||| b = mVC a `vcConcurrent` mVC b
{-@ reflect |||| @-}



-- ** Deliverable predicate

{-@
deliverable :: m:M r -> VCasM {m} -> Bool @-}
deliverable :: M r -> VC -> Bool
deliverable m pVC =
    let n = listLength pVC -- QQQ: do we want an alias for proc-count?
    in listAnd (listZipWith3 (deliverableHelper (mSender m)) (fin n) (mVC m) pVC)
{-@ reflect deliverable @-}

{-@
deliverableHelper :: PID -> PID -> Clock -> Clock -> Bool @-}
deliverableHelper :: PID -> PID -> Clock -> Clock -> Bool
deliverableHelper i k vc_m_k vc_p_k -- i is sender PID, k is current PID/index.
    | k == i    = vc_m_k == vc_p_k + 1
    | otherwise = vc_m_k <= vc_p_k
{-@ reflect deliverableHelper @-}



-- ** Delay queue

-- QQQ: to show PLCD do we need to know the order of messages in the DQ?

{-@
enqueue :: m:M r -> DQasM r {m} -> DQasM r {m} @-}
enqueue :: M r -> DQ r -> DQ r
enqueue m [] = [m]
enqueue m (x:xs)
    | m ===> x  = m:x:xs -- Messages are in order of their vector clocks.
    | m |||| x  = x:enqueue m xs -- Concurrent messages are in receipt order.
    | otherwise = x:enqueue m xs
{-@ reflect enqueue @-}

{-@
dequeue :: v:VC -> DQasV r {v} -> Maybe (MasV r {v}, DQasV r {v}) @-}
dequeue :: VC -> DQ r -> Maybe (M r, DQ r)
dequeue _now [] = Nothing
dequeue now (x:xs)
    | deliverable x now = Just (x, xs)
    | otherwise =
        case dequeue now xs of -- Skip past x.
            Nothing -> Nothing
            Just (m, xs') -> Just (m, x:xs')
{-@ reflect dequeue @-}



-- ** Tick

-- QQQ: do we want to try to constrain the PID to be a valid index to the VC?

{-@
tick :: _ -> v:VC -> VCasV {v} @-}
tick :: PID -> VC -> VC
tick pid now | pid < 0 = now    -- NOTE: was not valid, pid < 0
tick _pid [] = []               -- NOTE: was not valid, procCount <= pid
tick 0 (x:xs) = (x + 1) : xs
tick pid (x:xs) = x : tick (pid - 1) xs
{-@ reflect tick @-}



-- ** Causal Delivery state machine

-- | Put a message in the dq.
{-@
receive :: m:M r -> PasM r {m} -> PasM r {m} @-}
receive :: M r -> P r -> P r
receive m p@P{dq} =
    p{dq=enqueue m dq}
{-@ reflect receive @-}

-- | Get a message from the dq, update the local vc and history. After this,
-- the UAP should consume the message.
{-@
deliver :: p:P r -> Maybe (MasP r {p}, PasP r {p}) @-}
deliver :: P r -> Maybe (M r, P r)
deliver p@P{pid,pVC,dq,hist} =
    case dequeue pVC dq of
        Nothing -> Nothing
        Just (m, dq') -> Just (m, p
            { pVC = listZipWith ordMax pVC (mVC m) -- Could use tick here.
            , dq = dq'
            , hist =
                (if pid == mSender m
                then Broadcast (coerce m) -- Note: This is a design choice.
                else Deliver pid (coerce m)) : hist
            })
{-@ reflect deliver @-}

-- | Prepare a message for broadcast.
--
-- After this, MPA must also convey M to this process via receive and then
-- deliver, in that way updating the local process VC. This could be done by
-- sending over the network, but that's not advised. Instead, use
-- @broadcastCycle@ below.
{-@
prepareBroadcast :: r -> p:P r -> MasP r {p} @-}
prepareBroadcast :: r -> P r -> M r
prepareBroadcast mRaw P{pid,pVC} =
    let vcmmSent = tick pid pVC -- NOTE: since we don't constrain pid, TICKing doesn't guarantee any change.
        mMetadata = VCMM{vcmmSent, vcmmSender=pid}
    in Message{mMetadata, mRaw}
{-@ reflect prepareBroadcast @-}

{-@
broadcastCycleAlwaysDelivers :: msg:_ -> p:_ -> {Nothing /= deliver (receive (prepareBroadcast msg p) p)} @-}
broadcastCycleAlwaysDelivers :: r -> P r -> Proof
broadcastCycleAlwaysDelivers _msg _p = () *** Admit

-- | Prepare a message for broadcast, put it into this process's delay queue,
-- and then perform a normal delivery. After this, the UAP should consume the
-- message.
broadcast :: r -> P r -> (M r, P r)
broadcast raw p =
    case deliver (receive (prepareBroadcast raw p) p)
    `proofConst` broadcastCycleAlwaysDelivers raw p of
        Just tup -> tup
{-@ reflect broadcast @-}

--{-@
--broadcastIsDeliverable :: msg:_ -> p:_ -> {deliverable (broadcast msg p) (vc_p p)} @-}
--broadcastIsDeliverable :: String -> P -> Proof
--broadcastIsDeliverable _msg _p = () *** Admit
--
--
---- * Process local causal delivery
--
---- | If events A, B, and C occur, history will be C:B:A:[]. Process order e->e'
---- indicates that e appears in the subsequence prior to e'.
--processOrder :: [E] -> E -> E -> Bool
--processOrder hist e e' = listElem e (listTailForHead e' hist)
--
---- {-@
---- processLocalCausalDelivery H P = {m:_ | listElem (D P m) -> m':_
