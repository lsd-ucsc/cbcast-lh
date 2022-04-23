{-# OPTIONS_GHC "-Wno-warnings-deprecations" #-} -- Hide the "verification only" and "internal use" warnings

-- | Properties concerning CBCAST.Core
module CBCAST.Verification.Core {-# WARNING "Verification only" #-} where

import Language.Haskell.Liquid.ProofCombinators (Proof, (===), (***), QED(..), (?), impossible)

import Redefined
import Redefined.Verification
import VectorClock
import VectorClock.Verification
import CBCAST.Core




-- * Lemmas for Broadcast always delivers

-- | Ticking a process VC results in a VC which is deliverable at that process.
--
{-@ ple deliverableAfterTick @-}
{-@
deliverableAfterTick
    ::  raw:r
    -> p_vc:VC
    -> p_id:PIDasV {p_vc}
    -> { deliverable (Message (vcTick p_vc p_id) p_id raw) p_vc }
@-}
deliverableAfterTick :: r -> VC -> PID -> Proof
deliverableAfterTick raw p_vc p_id
    =   let n = vcSize p_vc
            m = Message (vcTick p_vc p_id) p_id raw
    in  deliverable m p_vc -- restate conclusion
    === listAnd (listZipWith3 (deliverableHelper (mSender m)) (finAsc n) (mVC m) p_vc) -- by def of deliverable
    === listAnd (listZipWith3 (deliverableHelper p_id) (finAscHelper 0 n) (vcTick p_vc p_id) p_vc) -- by def of mSender,finAsc,mVC
        ? deliverableAfterTick_lemma 0 n p_vc p_id
    *** QED

-- | Lemma to show that ticking a process VC results in a VC which is
-- deliverable at that process. Induction over index into VC @m@, with base
-- case at @m@ equal to the length of VCs @n@.
--
{-@ ple deliverableAfterTick_lemma @-}
{-@
deliverableAfterTick_lemma
    ::    m:Nat
    ->   {n:Nat | m <= n}
    -> p_vc:VCsized {n - m}
    -> p_id:PIDsized {n}
    -> {
        listAnd (listZipWith3
                        (deliverableHelper p_id)
                        (finAscHelper m n)
                        (if m<=p_id then (vcTick p_vc (p_id-m)) else p_vc)
                        p_vc
                    )
        }
@-}
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




-- * Lemmas for PLCD preservation

{-@
dequeueImpliesDeliverable
    ::  vc:VC
    -> {dq:DQasV r {vc} | isJust (dequeue vc dq)}
    -> { deliverable (fst (fromJust (dequeue vc dq))) vc }
@-}
dequeueImpliesDeliverable :: VC -> DQ r -> Proof
dequeueImpliesDeliverable vc [] =   impossible
    {-restate premise-}         $   dequeue vc []
    {-by def of dequeue-}       === Nothing
dequeueImpliesDeliverable vc (x:xs)
    | deliverable x vc =
        {-restate premise-}         dequeue vc (x:xs)
        {-by def of deliverable-}   === Just (x, xs)
        {-by case assumption-}      *** QED
    | otherwise =
        case dequeue vc xs of
            Nothing ->                          impossible
                {-restate premise-}         $   dequeue vc (x:xs)
                {-by def of deliverable-}   === Nothing
            Just (m, xs') ->
                {-restate premise-}                 dequeue vc (x:xs)
                {-by def of deliverable-}           === Just (m, x:xs')
                ? dequeueImpliesDeliverable vc xs   *** QED

{-@
deliverableImpliesNotVCLessEqual
    ::      m:Message r
    -> { p_vc:VCasM {m} | deliverable m p_vc }
    -> { not (vcLessEqual (mVC m) p_vc) }
@-}
deliverableImpliesNotVCLessEqual :: Message r -> VC -> Proof
deliverableImpliesNotVCLessEqual m p_vc =
                            let n = vcSize p_vc in
    {-restate theorem-}         (if deliverable m p_vc then not (vcLessEqual (mVC m) p_vc) else True)
    {-∀a,b.(a⇒b)⇔(¬a∨b)-}   === (not (deliverable m p_vc) || not (vcLessEqual (mVC m) p_vc))
    {-∀a,b.¬(a∧b)⇔(¬a∨¬b)-} === not (deliverable m p_vc && vcLessEqual (mVC m) p_vc)
    {-by def of deliverable,vcLessEqual-}
                            === not ( listAnd (listZipWith3 (deliverableHelper (mSender m)) (finAsc n) (mVC m) p_vc)
                                   && listAnd (listZipWith vcLessEqualHelper (mVC m) p_vc) )
    ? deliverableImpliesNotVCLessEqual_lemma 0 n (mSender m) (mVC m) p_vc
                            === True
                            *** QED

{-@
deliverableImpliesNotVCLessEqual_lemma
    ::        lb:Nat
    ->       {ub:Nat | lb <= ub}
    -> {m_sender:PIDsized {ub} | lb <= m_sender}
    ->      m_vc:VCsized {ub - lb}
    ->      p_vc:VCsized {ub - lb}
    -> { not ( listAnd (listZipWith3 (deliverableHelper m_sender) (finAscHelper lb ub) m_vc p_vc)
            && listAnd (listZipWith vcLessEqualHelper m_vc p_vc) ) }
@-}
deliverableImpliesNotVCLessEqual_lemma :: Int -> Int -> PID -> VC -> VC -> Proof
deliverableImpliesNotVCLessEqual_lemma lb ub m_sender (m_vc_k:m_vc) (p_vc_k:p_vc)
    -- by cases of deliverableHelper
    | lb == m_sender
        {-restate conclusion-}          =   not (listAnd (listZipWith3 (deliverableHelper m_sender) (finAscHelper lb ub) (m_vc_k:m_vc) (p_vc_k:p_vc)) && listAnd (listZipWith vcLessEqualHelper (m_vc_k:m_vc) (p_vc_k:p_vc)))
        {-by def of finAscHelper-}      === not (listAnd (listZipWith3 (deliverableHelper m_sender) (lb:finAscHelper (lb+1) ub) (m_vc_k:m_vc) (p_vc_k:p_vc)) && listAnd (listZipWith vcLessEqualHelper (m_vc_k:m_vc) (p_vc_k:p_vc)))
        {-by def of zipWith3,zipWith-}  === not (listAnd (deliverableHelper m_sender lb m_vc_k p_vc_k : listZipWith3 (deliverableHelper m_sender) (finAscHelper (lb+1) ub) (m_vc) (p_vc)) && listAnd (vcLessEqualHelper m_vc_k p_vc_k : listZipWith vcLessEqualHelper m_vc p_vc))
        {-by def of listAnd-}           === not (deliverableHelper m_sender lb m_vc_k p_vc_k && listAnd (listZipWith3 (deliverableHelper m_sender) (finAscHelper (lb+1) ub) (m_vc) (p_vc)) && vcLessEqualHelper m_vc_k p_vc_k && listAnd (listZipWith vcLessEqualHelper m_vc p_vc))
        {-∀a,b.¬(a∧b)⇔(¬a∨¬b)-}         === not (deliverableHelper m_sender lb m_vc_k p_vc_k && vcLessEqualHelper m_vc_k p_vc_k)
        {-by defs of helpers-}          === not (m_vc_k == p_vc_k + 1 && m_vc_k <= p_vc_k)
        *** QED
    | lb < m_sender
        {-restate conclusion-}          =   not (listAnd (listZipWith3 (deliverableHelper m_sender) (finAscHelper lb ub) (m_vc_k:m_vc) (p_vc_k:p_vc)) && listAnd (listZipWith vcLessEqualHelper (m_vc_k:m_vc) (p_vc_k:p_vc)))
        {-by def of finAscHelper-}      === not (listAnd (listZipWith3 (deliverableHelper m_sender) (lb:finAscHelper (lb+1) ub) (m_vc_k:m_vc) (p_vc_k:p_vc)) && listAnd (listZipWith vcLessEqualHelper (m_vc_k:m_vc) (p_vc_k:p_vc)))
        {-by def of zipWith3,zipWith-}  === not (listAnd (deliverableHelper m_sender lb m_vc_k p_vc_k : listZipWith3 (deliverableHelper m_sender) (finAscHelper (lb+1) ub) (m_vc) (p_vc)) && listAnd (vcLessEqualHelper m_vc_k p_vc_k : listZipWith vcLessEqualHelper m_vc p_vc))
        {-by def of listAnd-}           === not (deliverableHelper m_sender lb m_vc_k p_vc_k && listAnd (listZipWith3 (deliverableHelper m_sender) (finAscHelper (lb+1) ub) (m_vc) (p_vc)) && vcLessEqualHelper m_vc_k p_vc_k && listAnd (listZipWith vcLessEqualHelper m_vc p_vc))
        {-associativity of ∧-}          === not (deliverableHelper m_sender lb m_vc_k p_vc_k && vcLessEqualHelper m_vc_k p_vc_k
                                                && listAnd (listZipWith3 (deliverableHelper m_sender) (finAscHelper (lb+1) ub) (m_vc) (p_vc)) && listAnd (listZipWith vcLessEqualHelper m_vc p_vc))
        ? deliverableImpliesNotVCLessEqual_lemma (lb+1) ub m_sender m_vc p_vc
                                        === not (deliverableHelper m_sender lb m_vc_k p_vc_k && vcLessEqualHelper m_vc_k p_vc_k && False)
        *** QED




-- * Lemmas about histVC

isDeliver :: Event r -> Bool
isDeliver Deliver{} = True
isDeliver _ = False
{-@ inline isDeliver @-}

-- | VCs deliveries in the history are all less-equal than histVC.
{-@
histElemLessEqualHistVC
    ::     n:Nat
    -> {   e:Esized r {n} | isDeliver e }
    -> { hhs:Hsized r {n} | listElem e hhs }
    -> { vcLessEqual (mVC (eventMessage e)) (histVC n hhs) }
@-}
histElemLessEqualHistVC :: Eq r => Int -> Event r -> ProcessHistory r -> Proof
-- 1/3) empty history
histElemLessEqualHistVC _n e@Deliver{} [] =
    impossible $ listElem e [] -- restate (failed) premise
-- 2/3) history with broadcast at head
histElemLessEqualHistVC n e@Deliver{} (h@Broadcast{}:hs) =
    let
    eVC = mVC (eventMessage e)
    hsVC = histVC n hs
    hhsVC = histVC n (h:hs)
    in
                                        True
    ? tailElem e h hs                   === listElem e hs
    ? histElemLessEqualHistVC n e hs    === eVC `vcLessEqual` hsVC
    ? hsVC == hhsVC {-h is Broadcast-}  === eVC `vcLessEqual` hhsVC
                                        *** QED
-- 3/3) history with deliver at head
histElemLessEqualHistVC n e@Deliver{} (h@Deliver{}:hs)
  | e == h =
                                        True
    ? vcCombineResultLarger hVC hsVC    === hVC `vcLessEqual` hhsVC
                                        *** QED
  | otherwise =
                                                True
    ? tailElem e h hs                           === listElem e hs
    ? histElemLessEqualHistVC n e hs            === eVC `vcLessEqual` hsVC
    ? vcCombineResultLarger hVC hsVC            === hsVC `vcLessEqual` hhsVC
    ? vcLessEqualTransitive n eVC hsVC hhsVC    === eVC `vcLessEqual` hhsVC
                                                *** QED
  where
    eVC = mVC (eventMessage e)
    hVC = mVC (eventMessage h)
    hsVC = histVC n hs
    hhsVC = histVC n (h:hs)
        === hVC `vcCombine` hsVC -- h is Deliver
