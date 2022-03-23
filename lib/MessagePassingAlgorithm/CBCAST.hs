
-- | CBCAST is a causal delivery message passing algorithm implemented using
-- vector clocks and receiver side buffering.
module MessagePassingAlgorithm.CBCAST where

import Language.Haskell.Liquid.ProofCombinators
import Language.Haskell.Liquid.ProofCombinatorsExtra

import Redefined
import VectorClock
import MessagePassingAlgorithm
import MessagePassingAlgorithm.VectorClockAdapter




-- * Datatypes

-- | Delay queue sorted by vector clocks (lesser to the left) with concurrent
-- messages in order of receipt (older to the left).
type DQ r = [M r]
{-@ type DQsized r N = [Msized r {N}] @-}
{-@ type DQasV r V = DQsized r {len V} @-}
{-@ type DQasM r M = DQsized r {len (mVC M)} @-}

-- | Process structure with an explicit history of local broadcast and delivery
-- events.
data P r = P {pVC::VC, pID::PID, pDQ::DQ r, pHist::H r}
{-@
data P r = P
    { pVC :: VC
    , pID :: PIDasV {pVC}
    , pDQ :: DQsized r {len pVC}
    , pHist :: {h:Hsized r {len pVC} | histVC (len pVC) h == pVC}
    }
@-}
{-@ type Psized r N = {p:P r | len (pVC p) == N} @-}
{-@ type PasP r P = Psized r {len (pVC P)} @-}
{-@ type PasM r M = Psized r {len (mVC M)} @-}

{-@ type VCasP P = VCsized {len (pVC P)} @-}

{-@ type MasP r P = Msized r {len (pVC P)} @-}




-- * Initialization

-- | The empty, initial, p₀, for processes.
{-@
pEmpty :: n:Nat -> PIDsized {n} -> Psized r {n} @-}
pEmpty :: Int -> PID -> P r
pEmpty n p_id = P
    { pVC = vcEmpty n
    , pID = p_id
    , pDQ = []
    , pHist = []
        `proofConst` pEmptyCHA n -- CHA_MIGRATION
    }
{-@ reflect pEmpty @-}




-- * Deliverable predicate

-- | Is the message (with its sent vector clock and sender PID) deliverable at
-- the local vector clock?
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




-- * Delay queue operations

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




-- * Causal Delivery state machine

-- | Put a message in the dq. Messages with the sender ID of the current
-- process are ignored. The MPA should use this for messages from the network.
{-@
internalReceive :: m:M r -> PasM r {m} -> PasM r {m} @-}
internalReceive :: M r -> P r -> P r
internalReceive m p
    | mSender m == pID p = p -- NOTE: Ignores network messages with local pid
    | otherwise = p{ pDQ = enqueue m (pDQ p) }
{-@ reflect internalReceive @-}

-- | Get a message from the dq, update the local vc and history. After this,
-- the MPA should pass the message to the UAP for processing.
{-@
internalDeliver :: p:P r -> Maybe (MasP r {p}, PasP r {p}) @-}
internalDeliver :: P r -> Maybe (M r, P r)
internalDeliver p =
    case dequeue (pVC p) (pDQ p) of
        Nothing -> Nothing
        Just (m, pDQ') -> Just (m, p
            { pVC = vcCombine (mVC m) (pVC p) -- Could use tick here.
            , pDQ = pDQ'
            , pHist = Deliver (pID p) (coerce m) : pHist p
                `proofConst` internalDeliverCHA m (pID p) (pVC p) (pHist p) -- CHA_MIGRATION
            })
{-@ reflect internalDeliver @-}

-- | Prepare a message for broadcast, put it into this process's delay queue,
-- and then perform a normal delivery. After this, the MPA should place the
-- message on the network and pass the message to the UAP for processing.
{-@
internalBroadcast :: r -> p:P r -> (MasP r {p}, PasP r {p}) @-}
internalBroadcast :: r -> P r -> (M r, P r)
internalBroadcast raw p₀ =
    let m = broadcastHelper_prepareMessage raw p₀
        p₁ = broadcastHelper_injectMessage m p₀
    in case internalDeliver p₁ `proofConst` broadcastAlwaysDelivers raw p₀ of
            Just tup -> tup
{-@ reflect internalBroadcast @-}

-- | Helper for internalBroadcast
{-@
broadcastHelper_prepareMessage :: r -> p:P r -> MasP r {p} @-}
broadcastHelper_prepareMessage :: r -> P r -> M r
broadcastHelper_prepareMessage raw p = Message
    { mMetadata = VCMM
        { vcmmSent = vcTick (pVC p) (pID p)
        , vcmmSender = pID p }
    , mRaw = raw }
{-@ reflect broadcastHelper_prepareMessage @-}

-- | Helper for internalBroadcast
{-@
broadcastHelper_injectMessage :: m:M r -> PasM r {m} -> PasM r {m} @-}
broadcastHelper_injectMessage :: M r -> P r -> P r
broadcastHelper_injectMessage m p = p
    { pDQ = m : pDQ p
    , pHist = Broadcast (coerce m) : pHist p
        `proofConst` internalBroadcastCHA m (pVC p) (pHist p) -- CHA_MIGRATION
    }
{-@ reflect broadcastHelper_injectMessage @-}




-- * Clock-history agreement

-- CHA_MIGRATION: This isn't part of the implementation. It is used as in a
-- constraint on the Process structure.

{-@ cha2predicate :: v:VC -> Hsized r {len v} -> Bool @-}
cha2predicate :: VC -> H r -> Bool
cha2predicate v h =
    v == histVC (listLength v) h
{-@ inline cha2predicate @-}

{-@ type CHA2property V H =
        {_ : Proof | cha2predicate V H } @-}

{-@ pEmptyCHA :: n:Nat -> CHA2property {vcEmpty n} {[]} @-} -- CHA_MIGRATION
pEmptyCHA :: Int -> Proof
pEmptyCHA n =
        histVC n []
    === vcEmpty n
    *** QED

{-@ type CHA2preservation N VF HF =
        v:VCsized {N} -> {h:Hsized r {N} | cha2predicate v h} -> CHA2property {VF v} {HF h} @-}

{-@
internalDeliverCHA
    ::    m:M r
    -> p_id:PIDasM {m}
    -> CHA2preservation {len (mVC m)} {vcCombine (mVC m)} {cons (Deliver p_id m)} @-}
internalDeliverCHA :: M r -> PID -> VC -> H r -> Proof
internalDeliverCHA m p_id p_vc p_hist =
    let
    p_vc' = vcCombine (mVC m) p_vc
    n = listLength p_vc'
    e = Deliver p_id (coerce m)
    in
        histVC n (e : p_hist)
    === mVC (eventMessage n e) `vcCombine` histVC n p_hist
    === mVC m `vcCombine`  p_vc
    *** QED

{-@
internalBroadcastCHA
    ::    m:M r
    -> CHA2preservation {len (mVC m)} {identity} {cons (Broadcast m)} @-}
internalBroadcastCHA :: M r -> VC -> H r -> Proof
internalBroadcastCHA m p_vc p_hist =
    let
    n = listLength p_vc
    e = Broadcast (coerce m)
    in
        histVC n (e : p_hist)
    === p_vc
    *** QED




-- * Proof that internalBroadcast always delivers

-- | Broadcast's call to deliver will always return the message just produced
-- by the prepare message helper (not @Nothing@).
{-@ ple broadcastAlwaysDelivers @-}
{-@
broadcastAlwaysDelivers
    :: raw:r
    -> p:P r
    -> { isJust (internalDeliver (broadcastHelper_injectMessage (broadcastHelper_prepareMessage raw p) p))
    && fst (fromJust (internalDeliver (broadcastHelper_injectMessage (broadcastHelper_prepareMessage raw p) p)))
    == broadcastHelper_prepareMessage raw p }
@-}
broadcastAlwaysDelivers :: r -> P r -> Proof
broadcastAlwaysDelivers raw p₀ =
    let
        m = broadcastHelper_prepareMessage raw p₀
        p₁ = broadcastHelper_injectMessage m p₀
            --- QQQ: Why does this step require PLE?
            === p₀
                { pDQ = m : pDQ p₀
                , pHist = Broadcast (coerce m) : pHist p₀
                    `proofConst` internalBroadcastCHA m (pVC p₀) (pHist p₀) -- CHA_MIGRATION
                }
        dequeueBody
            = dequeue (pVC p₁) (pDQ p₁)
            === dequeue (pVC p₁) (m : pDQ p₀)
                ? deliverableNewMessage raw p₀
                -- QQQ: Why is PLE necessary for this step?
            === Just (m, pDQ p₀)
        deliverBody
            = internalDeliver p₁
                ? dequeueBody
            === Just (m, p₁
                { pVC = vcCombine (mVC m) (pVC p₁)
                , pDQ = pDQ p₀
                , pHist = Deliver (pID p₁) (coerce m) : pHist p₁
                    `proofConst` internalDeliverCHA m (pID p₁) (pVC p₁) (pHist p₁) -- CHA_MIGRATION
                })
    in
    deliverBody *** QED

-- | Broadcast's prepare message helper produces messages deliverable at the
-- producing process process.
{-@ ple deliverableNewMessage @-}
{-@
deliverableNewMessage :: raw:_ -> p:_ -> {deliverable (broadcastHelper_prepareMessage raw p) (pVC p)} @-}
deliverableNewMessage :: r -> P r -> Proof
deliverableNewMessage raw p
    =   deliverable (broadcastHelper_prepareMessage raw p) (pVC p) -- restate conclusion
    --- QQQ: Why does this step require PLE?
    === deliverable (Message (VCMM (vcTick (pVC p) (pID p)) (pID p)) raw) (pVC p) -- by definition of broadcastHelper_prepareMessage
        ? deliverableAfterTick raw (pVC p) (pID p)
    *** QED

-- | Ticking a process VC results in a VC which is deliverable at that process.
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

-- | Lemma to show that ticking a process VC results in a VC which is
-- deliverable at that process. Induction over index into VC @m@, with base
-- case at @m@ equal to the length of VCs @n@.
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
