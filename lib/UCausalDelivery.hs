{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}
-- {-# LANGUAGE NoFieldSelectors #-}
{-# LANGUAGE NamedFieldPuns #-}
module UCausalDelivery where

import Language.Haskell.Liquid.ProofCombinators
import Redefined.Fin

import SystemModel
import Properties ()

-- * Causal Delivery MPA



-- ** This MPA uses VCs

{-@ type VCasM M = VCsized {mProcCount M} @-}

{-@
type M r = Message VCMM r @-}
type M r = Message VCMM r
{-@ type Msized r N = {m:M r | mProcCount m == N} @-}
{-@ type Mas r M = Msized r {mProcCount M} @-}
{-@ type MasV r V = Msized r {len V} @-}

{-@
type H r = ProcessHistory VCMM r @-}
type H r = ProcessHistory VCMM r

-- QQQ: Do we want to push these convenence aliases into the system model? Is
-- the definition of PLCD hard to read?



-- ** Message order

{-@
(===>) :: x:M r -> Mas r {x} -> Bool @-}
(===>) :: M r -> M r -> Bool
a ===> b = mVC a `vcLess` mVC b
{-@ reflect ===> @-}

{-@
(||||) :: x:M r -> Mas r {x} -> Bool @-}
(||||) :: M r -> M r -> Bool
a |||| b = mVC a `vcConcurrent` mVC b
{-@ reflect |||| @-}



-- ** Deliverable predicate

{-@
deliverable :: m:M r -> VCasM {m} -> Bool @-}
deliverable :: M r -> VC -> Bool
deliverable m pVC =
    let n = mProcCount m
    -- NOTE: this listZipWith3 requires its arguments to be the same length
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

type DQ r = [M r]
{-@ type DQsized r N = [Msized r {N}] @-}
{-@ type DQasV r V = DQsized r {len V} @-}
{-@ type DQasM r M = DQsized r {mProcCount M} @-}

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
tick :: _ -> v:VC -> VCas {v} @-}
tick :: PID -> VC -> VC
tick pid now | pid < 0 = now    -- NOTE: was not a valid pid
tick _pid [] = []               -- NOTE: was not a valid pid
tick 0 (x:xs) = (x + 1) : xs
tick pid (x:xs) = x : tick (pid - 1) xs
{-@ reflect tick @-}



{-@
data P = P {pid::PID, vc_p::VC, dq::DQ, hist::[M]} @-}
data P = P {pid::PID, vc_p::VC, dq::DQ, hist::[M]}

-- | Put a message in the dq.
{-@ reflect receive @-}
receive :: M -> P -> P
receive m p@P{dq} =
    p{dq=enqueue m dq}

-- | Get a message from the dq and update the local VC.
{-@ reflect deliver @-}
deliver :: P -> Maybe (M, P)
deliver p@P{vc_p,dq} =
    case dequeue vc_p dq of
        Nothing -> Nothing
        Just (m@M{vc_m}, dq') ->
            let vc_p' = listZipWith ordMax vc_p vc_m -- Could use tick here.
            in Just (m, p{vc_p=vc_p', dq=dq'})

-- | Prepare a message for broadcast.
--
-- Must also convey M to this process via receive and then deliver, in that way
-- updating the local process VC. You can do this by sending over the network,
-- but that's not advised.
{-@ reflect broadcast @-}
broadcast :: String -> P -> M
broadcast msg P{pid,vc_p} =
    let vc_m = tick pid vc_p
    in M{sender=pid, vc_m, msg}

-- | Prepare a message for broadcast, put it into this process's delay queue,
-- and then perform a normal delivery.
{-@ reflect broadcastCycle @-}
broadcastCycle :: String -> P -> (M, P)
broadcastCycle msg p =
    case deliver (receive (broadcast msg p) p)
    `proofConst` broadcastCycleAlwaysDelivers msg p of
        Just tup -> tup

-- -- {-@
-- -- broadcastIs :: msg:_ -> p:_ -> {} @-}
-- 
-- {-@
-- broadcastIsDeliverable :: msg:_ -> p:_ -> {deliverable (broadcast msg p) (vc_p p)} @-}
-- broadcastIsDeliverable :: String -> P -> Proof
-- broadcastIsDeliverable msg p@P{vc_p}
--     =   deliverable (broadcast msg p) (vc_p p)
--     *** Admit

{-@
broadcastCycleAlwaysDelivers :: msg:_ -> p:_ -> {Nothing /= deliver (receive (broadcast msg p) p)} @-}
broadcastCycleAlwaysDelivers :: String -> P -> Proof
broadcastCycleAlwaysDelivers msg p = () *** Admit
-- ? broadcastIsDeliverable msg p
