
-- | CBCAST system model, process types, deliverable predicate, and delay queue
-- operations.
module CBCAST.Core where

import Language.Haskell.Liquid.ProofCombinators (Proof, (===), (***), QED(..))
import Language.Haskell.Liquid.ProofCombinatorsExtra (proofConst)

import Redefined
import VectorClock




-- * System model

{-@ type VCasM M = VCsized {messageSize M} @-}

-- | Process identifier
type PID = Fin
{-@ type PIDsized N = Fin {N} @-}
{-@ type PIDasV V = PIDsized {vcSize V} @-}
{-@ type PIDasM M = PIDsized {messageSize M} @-}

-- | Message structure with a vector clock, sender id, and raw content.
{-@
data Message r = Message {mVC::VC, mSender::PIDasV {mVC}, mRaw::r} @-}
data Message r = Message {mVC::VC, mSender::PID, mRaw::r}
    deriving Eq
{-@ type Msized r N = {m:Message r | messageSize m == N} @-}
{-@ type MasM r M = Msized r {messageSize M} @-}
{-@ type MasE r E = Msized r {eventSize E} @-}
{-@ type MasV r V = Msized r {vcSize V} @-}
{-@ type MasP r P = Msized r {processSize P} @-}

-- | Record of the act of broadcasting a message or delivering (to the user
-- local user application for processing) a message.
data Event r = Broadcast (Message r) | Deliver PID (Message r)
    deriving Eq
{-@ type Esized r N = {e:Event r | eventSize e == N} @-}

-- | History of events. Events are added to the left using cons (:). If events
-- 1, 2, and 3 occur, history will be 3:2:1:[].
type ProcessHistory r = [Event r]
{-@ type Hsized r N = [Esized r {N}] @-}
{-@ type HasV r V = Hsized r {vcSize V} @-}

-- MEASURE_ISSUE
messageSize :: Message r -> Int
messageSize m = vcSize (mVC m)
{-@ inline messageSize @-}
{-# WARNING messageSize "Verification only" #-}

-- MEASURE_ISSUE
eventMessage :: Event r -> Message r
eventMessage (Broadcast m) = m
eventMessage (Deliver _pid m) = m
{-@ inline eventMessage @-}
{-# WARNING eventMessage "Verification only" #-}

-- MEASURE_ISSUE
eventSize :: Event r -> Int
eventSize e = messageSize (eventMessage e)
{-@ inline eventSize @-}
{-# WARNING eventSize "Verification only" #-}




-- ** Convenience operators

-- | Message order convenience operator @a ===> b@ is true when the vector
-- clock in @a@ is less than that of @b@.
{-@
(===>) :: m:Message r -> MasM r {m} -> Bool @-}
(===>) :: Message r -> Message r -> Bool
a ===> b = mVC a `vcLess` mVC b
{-@ reflect ===> @-}

-- | Message order convenience operator @a |||| b@ is true when the vector
-- clock in @a@ is concurrent with that of @b@.
{-@
(||||) :: m:Message r -> MasM r {m} -> Bool @-}
(||||) :: Message r -> Message r -> Bool
a |||| b = mVC a `vcConcurrent` mVC b
{-@ reflect |||| @-}




-- * CBCAST

-- | Delay queue sorted by vector clocks (lesser to the left) with concurrent
-- messages in order of receipt (older to the left).
type DQ r = [Message r]
{-@ type DQsized r N = [Msized r {N}] @-}
{-@ type DQasV r V = DQsized r {vcSize V} @-}
{-@ type DQasM r M = DQsized r {messageSize M} @-}

-- | Process structure with an explicit history of local broadcast and delivery
-- events.
data Process r = Process
    { pVC :: VC
    , pID :: PID
    , pDQ :: DQ r
    , pHist :: ProcessHistory r
    }
{-@
data Process r = Process
    { pVC :: VC
    , pID :: PIDasV {pVC}
    , pDQ :: DQasV r {pVC}
    , pHist :: {h:HasV r {pVC} | chaPredicate pVC h }
    }
@-}
{-@ type Psized r N = {p:Process r | processSize p == N} @-}
{-@ type PasP r P = Psized r {processSize P} @-}
{-@ type PasM r M = Psized r {messageSize M} @-}

-- MEASURE_ISSUE
processSize :: Process r -> Int
processSize p = vcSize (pVC p)
{-@ inline processSize @-}
{-# WARNING processSize "Verification only" #-}




-- ** Deliverable predicate

-- | Is the message (with its sent vector clock and sender PID) deliverable at
-- the local vector clock?
{-@
deliverable :: m:Message r -> VCasM {m} -> Bool @-}
deliverable :: Message r -> VC -> Bool
deliverable m p_vc =
    let n = vcSize p_vc
    in listAnd (listZipWith3 (deliverableHelper (mSender m)) (finAsc n) (mVC m) p_vc)
{-@ reflect deliverable @-}

{-@
deliverableHelper :: PID -> PID -> Clock -> Clock -> Bool @-}
deliverableHelper :: PID -> PID -> Clock -> Clock -> Bool
deliverableHelper m_id k m_vc_k p_vc_k
    | k == m_id = m_vc_k == p_vc_k + 1
    | otherwise = m_vc_k <= p_vc_k
{-@ reflect deliverableHelper @-}




-- ** Delay queue operations

-- {-@ coerceDQ :: m:Message r -> DQasM r {m} -> [Msized r {messageSize m}] @-} -- BAD
-- {-@ coerceDQ :: m:Message r -> DQasM r {m} -> DQsized r {messageSize m} @-} -- OK
-- {-@ coerceDQ :: m:Message r -> DQasM r {m} -> DQasM r {m} @-} -- OK
coerceDQ :: Message r -> DQ r -> DQ r
coerceDQ _m dq = dq
-- TYPE_ALIAS_ISSUE

{-@
enqueue :: m:Message r -> [Msized r {messageSize m}] -> [Msized r {messageSize m}] @-}
---- TYPE_ALIAS_ISSUE PREFER_BELOW
---- {-@
---- enqueue :: m:Message r -> DQasM r {m} -> DQasM r {m} @-}
enqueue :: Message r -> DQ r -> DQ r
enqueue m [] = [m]
enqueue m (x:xs)
    | m ===> x  = m:x:xs -- Messages are in order of their vector clocks.
    | m |||| x  = x:enqueue m xs -- Concurrent messages are in receipt order.
    | otherwise = x:enqueue m xs
{-@ reflect enqueue @-}

{-@
dequeue :: v:VC -> DQasV r {v} -> Maybe (MasV r {v}, DQasV r {v}) @-}
dequeue :: VC -> DQ r -> Maybe (Message r, DQ r)
dequeue _now [] = Nothing
dequeue now (x:xs)
    | deliverable x now = Just (x, xs)
    | otherwise =
        case dequeue now xs of -- Skip past x.
            Nothing -> Nothing
            Just (m, xs') -> Just (m, x:xs')
{-@ reflect dequeue @-}





-- ** Initialization

-- | The empty, initial, p₀, for processes.
{-@
pEmpty :: n:Nat -> PIDsized {n} -> Psized r {n} @-}
pEmpty :: Int -> PID -> Process r
pEmpty n p_id = Process
    { pVC = vcEmpty n
    , pID = p_id
    , pDQ = []
    , pHist = []
        `proofConst` pEmptyCHA n
    }
{-@ reflect pEmpty @-}




-- ** Clock history agreement

-- MEASURE_ISSUE DELETE_ME
{-@
histHeadE :: n:Nat -> {h:Hsized r {n} | h /= []} -> Esized r {n} @-}
histHeadE :: Int -> ProcessHistory r -> Event r
histHeadE _n (e:_es) = e
-- MEASURE_ISSUE DELETE_ME
{-@
histHeadM :: n:Nat -> {h:Hsized r {n} | h /= []} -> Msized r {n} @-}
histHeadM :: Int -> ProcessHistory r -> Message r
histHeadM _n (e:_es) = eventMessage e
-- MEASURE_ISSUE DELETE_ME
{-@
histHeadVC :: n:Nat -> {h:Hsized r {n} | h /= []} -> VCsized {n} @-}
histHeadVC :: Int -> ProcessHistory r -> VC
histHeadVC _n (e:_es) = mVC (eventMessage e)

-- | The supremum of vector clocks on delivered messages in a process history.
--
-- This takes an explicit `n` because the base case builds an empty VC and
-- because types like ProcessHistory and DQ can't be measured easily to obtain
-- the VC size.
{-@
histVC :: n:Nat -> Hsized r {n} -> VCsized {n} @-}
histVC :: Int -> ProcessHistory r -> VC
histVC n [] = vcEmpty n
histVC n (Broadcast{}:es) = histVC n es
-- MEASURE_ISSUE DELETE_CASES
-- histVC n (Deliver _pid Message{mVC}:es) = mVC -- `vcCombine` histVC n es
-- histVC n (Deliver _pid m:es) = mVC m -- `vcCombine` histVC n es
histVC n (e@Deliver{}:es) = mVC (eventMessage e) `vcCombine` histVC n es
{-@ reflect histVC @-}
{-# WARNING histVC "Verification only" #-}

-- | Supremum of VCs on message deliveries in history equals the given VC.
{-@ chaPredicate :: v:VC -> HasV r {v} -> Bool @-}
chaPredicate :: VC -> ProcessHistory r -> Bool
chaPredicate v h =
    v == histVC (vcSize v) h
{-@ inline chaPredicate @-}
{-# WARNING chaPredicate "Verification only" #-}

{-@
type CHAproperty V H =
    {_ : Proof | chaPredicate V H } @-}

-- | For all VCs, V, and all process histories, H, if CHA holds of V with H,
-- then CHA holds of VF V with HF H.
{-@
type CHApreservation r N VF HF
    =   v:VCsized {N}
    -> {h:Hsized r {N} | chaPredicate v h}
    -> CHAproperty {VF v} {HF h}
@-}

{-@ pEmptyCHA :: n:Nat -> CHAproperty {vcEmpty n} {[]} @-}
pEmptyCHA :: Int -> Proof
pEmptyCHA n =
        histVC n []
    === vcEmpty n
    *** QED
{-# WARNING pEmptyCHA "Verification only" #-}
