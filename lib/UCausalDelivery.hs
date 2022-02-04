{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}
module UCausalDelivery where

import Language.Haskell.Liquid.ProofCombinators
import Redefined.Fin
import Redefined.Ord

import SystemModel
import Properties

-- * Causal Delivery MPA




-- ** VC sizing

-- How to compute VC sizes in refinements:
--
-- v:VC     len v
-- mm:VCMM  len (vcmmSent mm)
-- m:M r    len (mVC m)
-- p:P r    len (pVC p)

{-@ type VCasM M = VCsized {len (mVC M)} @-}
{-@ type VCasP P = VCsized {len (pVC P)} @-}

{-@ type VCMMsized N = {mm:VCMM | len (vcmmSent mm) == N} @-}
{-@ type VCMMasM M = VCMMsized {len (mVC M)} @-}

{-@
type M r = Message VCMM r @-} -- QQQ: Why is this required?
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
data P r = P {pVC::VC, pID::PIDasV {pVC}, pDQ::DQsized r {len pVC}, pHist::Hsized r {len pVC}} @-}
data P r = P {pVC::VC, pID::PID, pDQ::DQ r, pHist::H r}
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
deliverable m p_vc =
    let n = listLength p_vc -- QQQ: do we want an alias for proc-count?
    in listAnd (listZipWith3 (deliverableHelper (mSender m)) (finAsc n) (mVC m) p_vc)
{-@ reflect deliverable @-}

{-@
deliverableHelper :: PID -> PID -> Clock -> Clock -> Bool @-}
deliverableHelper :: PID -> PID -> Clock -> Clock -> Bool
deliverableHelper m_id k m_vc_k p_vc_k
    | k == m_id = m_vc_k == p_vc_k + 1
    | otherwise = m_vc_k <= p_vc_k
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




-- ** Tick & Combine

-- | Increment the ith offset into the VC (i=0 increments head).
{-@
vcTick :: v:VC -> PIDasV {v} -> VCasV {v} @-}
vcTick :: VC -> PID -> VC
vcTick (x:xs) 0 = (x + 1) : xs
vcTick (x:xs) i = x : vcTick xs (i - 1)
{-@ reflect vcTick @-}

{-@
vcCombine :: v:VC -> VCasV {v} -> VCasV {v} @-}
vcCombine :: VC -> VC -> VC
vcCombine = listZipWith ordMax
{-@ reflect vcCombine @-}
-- TODO: prove commutative




-- ** Causal Delivery state machine

-- | Put a message in the dq. Messages with the sender ID of the current
-- process are ignored. The MPA should use this for messages from the network.
{-@
receive :: m:M r -> PasM r {m} -> PasM r {m} @-}
receive :: M r -> P r -> P r
receive m p
    | mSender m == pID p = p -- NOTE: Ignores network messages with local pid
    | otherwise = p{ pDQ = enqueue m (pDQ p) }
{-@ reflect receive @-}

-- | Get a message from the dq, update the local vc and history. After this,
-- the MPA should pass the message to the UAP for processing.
{-@
deliver :: p:P r -> Maybe (MasP r {p}, PasP r {p}) @-}
deliver :: P r -> Maybe (M r, P r)
deliver p =
    case dequeue (pVC p) (pDQ p) of
        Nothing -> Nothing
        Just (m, pDQ') -> Just (m, p
            { pVC = vcCombine (pVC p) (mVC m) -- Could use tick here.
            , pDQ = pDQ'
            , pHist = Deliver (pID p) (coerce m) : pHist p
            })
{-@ reflect deliver @-}

-- | Prepare a message for broadcast, put it into this process's delay queue,
-- and then perform a normal delivery. After this, the MPA should place the
-- message on the network and pass the message to the UAP for processing.
{-@
broadcast :: r -> p:P r -> (MasP r {p}, PasP r {p}) @-}
broadcast :: r -> P r -> (M r, P r)
broadcast raw p =
    let m = broadcastHelper raw p
    in case deliver p
        { pDQ = enqueue m (pDQ p)
        , pHist = Broadcast (coerce m) : pHist p
        } of
            Just tup -> tup
            Nothing -> undefined -- FIXME !!!!!!
-- {-@ reflect broadcast @-}

{-@
broadcastHelper :: r -> p:P r -> MasP r {p} @-}
broadcastHelper :: r -> P r -> M r
broadcastHelper raw p = Message
    { mMetadata = VCMM
        { vcmmSent = vcTick (pVC p) (pID p) -- NOTE: since we don't constrain pID, TICKing doesn't guarantee any change.
        , vcmmSender = pID p }
    , mRaw = raw }
{-@ reflect broadcastHelper @-}




-- ** Proofs about the state machine

-- | A vc is LT its ticked self. (16-17s for the explicit proof, 3s for PLE)
{-@ ple vcLessAfterTick @-}
{-@
vcLessAfterTick :: p_vc:VC -> p_id:PIDasV {p_vc} -> {vcLess p_vc (vcTick p_vc p_id)} @-}
vcLessAfterTick :: VC -> PID -> Proof
vcLessAfterTick (x:xs) p_id
    | p_id == 0
        =   vcLess (x:xs) (vcTick (x:xs) 0) -- restate conclusion
        === vcLess (x:xs) (x+1:xs) -- by def of vcTick, p_id=0 case
        === (vcLessEqual (x:xs) (x+1:xs) && (x:xs) /= (x+1:xs)) -- by def of vcLess
        === (x<=x+1 && vcLessEqual xs xs && (x:xs) /= (x+1:xs)) -- by def of vcLessEqual
            ? vcLessEqualReflexive xs
        *** QED
    | otherwise
        =   vcLess (x:xs) (vcTick (x:xs) p_id) -- restate conclusion
        === vcLess (x:xs) (x:vcTick xs (p_id - 1)) -- by def of vcTick, p_id/=0 case
        === (vcLessEqual (x:xs) (x:vcTick xs (p_id - 1)) && (x:xs) /= (x:vcTick xs (p_id - 1))) -- by def of vcLess
        === (x<=x && vcLessEqual xs (vcTick xs (p_id - 1)) && (x:xs) /= (x:vcTick xs (p_id - 1))) -- by def of vcLessEqual
            ? vcLessAfterTick xs (p_id - 1)
        *** QED

-- | Like vcLessAfterTick, but for processes local clocks.
{-@ ple pVCvcLessNewMsg @-}
{-@
pVCvcLessNewMsg :: raw:_ -> p:_ -> {vcLess (pVC p) (mVC (broadcastHelper raw p))} @-}
pVCvcLessNewMsg :: r -> P r -> Proof
pVCvcLessNewMsg raw p@P{pVC=x:xs}
    =   vcLess (x:xs) (mVC (broadcastHelper raw p)) -- restate conclusion
    === vcLess (x:xs) (vcTick (x:xs) (pID p)) -- by def of mVC and broadcastHelper
        ? vcLessAfterTick (x:xs) (pID p)
    *** QED

{-@ ple deliverableAfterTick_lemma @-}
{-@
deliverableAfterTick_lemma :: m:Nat -> {n:Nat | m <= n} -> p_vc:VCsized {n-m} -> p_id:PIDsized {n}
    -> {listAnd (listZipWith3 (deliverableHelper p_id) (finAscHelper m n) (if m<=p_id then (vcTick p_vc (p_id-m)) else p_vc) p_vc)} @-}
deliverableAfterTick_lemma :: Int -> Int -> VC -> PID -> Proof
deliverableAfterTick_lemma m n [] p_id
    -- in all cases we know that m>p_id
    | m == n
            =   listAnd (listZipWith3 (deliverableHelper p_id) (finAscHelper m n) (if m<=p_id then (vcTick [] (p_id-m)) else []) []) -- restate conclusion
            === listAnd (listZipWith3 (deliverableHelper p_id) (finAscHelper m n) [] []) -- simplify ifthenelse
            === listAnd (listZipWith3 (deliverableHelper p_id) [] [] []) -- by def of finAscHelper
            === listAnd [] -- by def of listZipWith3
            === True -- by def of listAnd
            *** QED
deliverableAfterTick_lemma m n (x:xs) p_id
    -- in all cases we know that m<n
    | m <  p_id -- case where vcTick doesn't increment and deliverable checks m_vc_k<=p_vc_k
            =   listAnd (listZipWith3 (deliverableHelper p_id) (finAscHelper m n)       (if m<=p_id then (vcTick (x:xs) (p_id-m)) else (x:xs)) (x:xs)) -- restate conclusion
            === listAnd (listZipWith3 (deliverableHelper p_id) (finAscHelper m n)       (vcTick (x:xs) (p_id-m))                               (x:xs)) -- simplify ifthenelse
            === listAnd (listZipWith3 (deliverableHelper p_id) (m:finAscHelper (m+1) n) (vcTick (x:xs) (p_id-m))                               (x:xs)) -- by def of finAscHelper
            === listAnd (listZipWith3 (deliverableHelper p_id) (m:finAscHelper (m+1) n) (x : vcTick xs (p_id-m-1))                             (x:xs)) -- by def of vcTick
            === (deliverableHelper p_id m x x     && listAnd (listZipWith3 (deliverableHelper p_id) (finAscHelper (m+1) n) (vcTick xs (p_id-m-1)) xs)) -- by def of listAnd,listZip
            === (x <= x                           && listAnd (listZipWith3 (deliverableHelper p_id) (finAscHelper (m+1) n) (vcTick xs (p_id-m-1)) xs)) -- by def of deliverableHelper
            ===                                      listAnd (listZipWith3 (deliverableHelper p_id) (finAscHelper (m+1) n) (vcTick xs (p_id-m-1)) xs)  -- simplify inequality
                ? deliverableAfterTick_lemma (m+1) n xs p_id
            *** QED
    | m == p_id -- case where vcTick increments and deliverable checks m_vc_k==p_vc_k+1
            =   listAnd (listZipWith3 (deliverableHelper p_id) (finAscHelper m n)       (if m<=p_id then (vcTick (x:xs) (p_id-m)) else (x:xs)) (x:xs)) -- restate conclusion
            === listAnd (listZipWith3 (deliverableHelper p_id) (finAscHelper m n)       (vcTick (x:xs) 0)                                      (x:xs)) -- simplify ifthenelse, simplify p_id-m
            === listAnd (listZipWith3 (deliverableHelper p_id) (m:finAscHelper (m+1) n) (vcTick (x:xs) 0)                                      (x:xs)) -- by def of finAscHelper
            === listAnd (listZipWith3 (deliverableHelper p_id) (m:finAscHelper (m+1) n) (x+1 : xs)                                             (x:xs)) -- by def of vcTick
            === (deliverableHelper p_id m (x+1) x && listAnd (listZipWith3 (deliverableHelper p_id) (finAscHelper (m+1) n)  xs                    xs)) -- by def of listAnd,listZip
            === (x+1 == x + 1                     && listAnd (listZipWith3 (deliverableHelper p_id) (finAscHelper (m+1) n)  xs                    xs)) -- by def of deliverableHelper
            ===                                      listAnd (listZipWith3 (deliverableHelper p_id) (finAscHelper (m+1) n)  xs                    xs)  -- simplify inequality
                ? deliverableAfterTick_lemma (m+1) n xs p_id
            *** QED
    | m >  p_id -- case where vcTick returned the tail and deliverable checks m_vc_k<=p_vc_k
            =   listAnd (listZipWith3 (deliverableHelper p_id) (finAscHelper m n)       (if m<=p_id then (vcTick (x:xs) (p_id-m)) else (x:xs)) (x:xs)) -- restate conclusion
            === listAnd (listZipWith3 (deliverableHelper p_id) (finAscHelper m n)       (x:xs)                                                 (x:xs)) -- simplify ifthenelse
            === listAnd (listZipWith3 (deliverableHelper p_id) (m:finAscHelper (m+1) n) (x:xs)                                                 (x:xs)) -- by def of finAscHelper
            === (deliverableHelper p_id m x x     && listAnd (listZipWith3 (deliverableHelper p_id) (finAscHelper (m+1) n)  xs                    xs)) -- by def of listAnd,listZipWith3
            === (x <= x                           && listAnd (listZipWith3 (deliverableHelper p_id) (finAscHelper (m+1) n)  xs                    xs)) -- by def of deliverableHelper
            ===                                      listAnd (listZipWith3 (deliverableHelper p_id) (finAscHelper (m+1) n)  xs                    xs)  -- simplify inequality
                ? deliverableAfterTick_lemma (m+1) n xs p_id
            *** QED

{-@ ple deliverableAfterTick @-}
{-@
deliverableAfterTick :: raw:_ -> p_vc:VC -> p_id:PIDasV {p_vc}
    -> {deliverable (Message (VCMM (vcTick p_vc p_id) p_id) raw) p_vc} @-}
deliverableAfterTick :: r -> VC -> PID -> Proof
deliverableAfterTick raw p_vc p_id
    =   let n = listLength p_vc
            m = Message (VCMM (vcTick p_vc p_id) p_id) raw
    in  deliverable m p_vc -- restate conclusion
    === listAnd (listZipWith3 (deliverableHelper (mSender m)) (finAsc n) (mVC m) p_vc) -- by def of deliverable
    === listAnd (listZipWith3 (deliverableHelper p_id) (finAscHelper 0 n) (vcTick p_vc p_id) p_vc) -- by def of mSender,finAsc,mVC
        ? deliverableAfterTick_lemma 0 n p_vc p_id
    *** QED

{-@ ple deliverableNewMessage @-}
{-@
deliverableNewMessage :: raw:_ -> p:_ -> {deliverable (broadcastHelper raw p) (pVC p)} @-}
deliverableNewMessage :: r -> P r -> Proof
deliverableNewMessage raw p
    =   deliverable (broadcastHelper raw p) (pVC p) -- restate conclusion
    --- QQQ: Why does this step require PLE?
    === deliverable (Message (VCMM (vcTick (pVC p) (pID p)) (pID p)) raw) (pVC p) -- by definition of broadcastHelper
        ? deliverableAfterTick raw (pVC p) (pID p)
    *** QED



-- ** Clock-History agreement

-- | The empty, initial, vc₀, vector clock.
{-@
vcEmpty :: n:Nat -> VCsized {n} @-}
vcEmpty :: Int -> VC
vcEmpty 0 = []
vcEmpty n = 0 : vcEmpty (n - 1)
{-@ reflect vcEmpty @-}

-- | The vc for the message in an event.
{-@
eventVC :: n:Nat -> Event (VCMMsized {n}) r -> VCsized {n} @-}
eventVC :: Int -> Event VCMM r -> VC
eventVC _n (Broadcast m) = vcmmSent (mMetadata m) -- QQQ: Why can't we use mVC here?
eventVC _n (Deliver _pid m) = vcmmSent (mMetadata m)
{-@ reflect eventVC @-}

-- | The supremum of vector clocks on events in a process history.
{-@
pHistVC :: p:P r -> VCasP {p} @-}
pHistVC :: P r -> VC
pHistVC p = pHistVCHelper (listLength (pVC p)) (pHist p)
{-@ reflect pHistVC @-}
{-@
pHistVCHelper :: n:Nat -> Hsized r {n} -> VCsized {n} @-}
pHistVCHelper :: Int -> H r -> VC
pHistVCHelper n [] = vcEmpty n
pHistVCHelper n (e:es) = eventVC n e `vcCombine` pHistVCHelper n es
{-@ reflect pHistVCHelper @-}

-- | The empty, initial, p₀, for processes.
{-@
pEmpty :: n:Nat -> PIDsized {n} -> Psized r {n} @-}
pEmpty :: Int -> Fin -> P r
pEmpty n p_id = P{pVC=vcEmpty n, pID=p_id, pDQ=[], pHist=[]}
{-@ reflect pEmpty @-}

{-@
type ClockHistoryAgreement P
    = {_ : Proof | vcLessEqual (pHistVC P) (pVC P) }
@-}

{-@ ple pEmptyCHA @-}
{-@
pEmptyCHA :: n:Nat -> p_id:PIDsized {n} -> ClockHistoryAgreement {pEmpty n p_id} @-}
pEmptyCHA :: Int -> Fin -> Proof
pEmptyCHA n p_id
    =   let p = pEmpty n p_id
    in  vcLessEqual (pHistVC p) (pVC p) -- restate conclusion
        ? vcLessEqualReflexive (vcEmpty n)
    *** QED

{-@
type CHApreservation r OP
    =  p:P r
    -> ClockHistoryAgreement {p}
    -> ClockHistoryAgreement {OP p}
@-}

{-@
receiveCHApres :: m:_ -> CHApreservation r {receive m} @-}
receiveCHApres :: M r -> P r -> Proof -> Proof
receiveCHApres _m _p _cha = () *** Admit



-- ** Process Local Causal Delivery

-- An alias for the system model's PLCD in terms of the MPA's process type.
{-@
type PLCD r P
    = ProcessLocalCausalDelivery r {pID P} {pHist P}
@-}

{-@ ple pEmptyPLCD @-}
{-@
pEmptyPLCD :: n:Nat -> p_id:PIDsized {n} -> PLCD r {pEmpty n p_id} @-}
pEmptyPLCD :: Eq r => Int -> Fin -> (M r -> M r -> Proof)
pEmptyPLCD _n _p_id _m1 _m2 = () -- Premises don't hold.
--pEmptyPLCD n p_id m1 _m2
--    =   True
--    --- QQQ: Why doesn't this premise report as True without PLE?
--    === listElem (Deliver p_id m1) (pHist (pEmpty n p_id)) -- restate a premise
--    --- QQQ: Why doesn't expanding the definition of pEmpty work without PLE?
--    === listElem (Deliver p_id m1) (pHist P{pVC=vcEmpty n, pID=p_id, pDQ=[], pHist=[]}) -- by def of pEmpty
--    === listElem (Deliver p_id m1) [] -- by def of pHist
--    === False -- by def of listElem
--    *** QED -- premise failed

{-@
type PLCDpreservation r OP
    =  p:P r
    -> PLCD r {p}
    -> PLCD r {OP p}
@-}

{-@
receivePLCDpres :: m:_ -> PLCDpreservation r {receive m} @-}
receivePLCDpres :: M r -> P r -> (M r -> M r -> Proof) -> M r -> M r -> Proof
receivePLCDpres _m _p _plcd _m1 _m2 = () *** Admit

--
--
--
