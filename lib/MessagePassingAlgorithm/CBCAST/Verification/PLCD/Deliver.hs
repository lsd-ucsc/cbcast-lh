{-# OPTIONS_GHC "-Wno-unused-imports" #-}

-- Proof that delivery preserves PLCD.
module MessagePassingAlgorithm.CBCAST.Verification.PLCD.Deliver where

import Language.Haskell.Liquid.ProofCombinators
import Language.Haskell.Liquid.ProofCombinatorsExtra

import Redefined
import VectorClock
import MessagePassingAlgorithm
import MessagePassingAlgorithm.CBCAST
import MessagePassingAlgorithm.VectorClockAdapter

import Redefined.Verification
import VectorClock.Verification
import MessagePassingAlgorithm.VectorClockAdapter.Verification.ProcessLocalCausalDelivery
import MessagePassingAlgorithm.CBCAST.Verification.Shims
import MessagePassingAlgorithm.CBCAST.Verification.ClockHistoryAgreement
import MessagePassingAlgorithm.CBCAST.Verification.PLCD

-- TODO rename ${NOUN}${PROP}pres to ${NOUN}Preserves${PROP}

{-@
deliverableImpliesNotVCLessEqual_lemma
    ::  lb:Nat
    -> {ub:Nat | lb <= ub}
    -> {m_sender:PIDsized {ub} | lb <= m_sender}
    -> m_vc:VCsized {ub-lb}
    -> p_vc:VCsized {ub-lb}
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

{-@
deliverableImpliesNotVCLessEqual
    :: m:M r
    -> { p_vc:VCasM {m} | deliverable m p_vc }
    -> { not (vcLessEqual (mVC m) p_vc) }
@-}
deliverableImpliesNotVCLessEqual :: M r -> VC -> Proof
deliverableImpliesNotVCLessEqual m p_vc =
                            let n = listLength p_vc in
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
dequeueImpliesDeliverable
    :: vc:VC
    -> {dq:DQasV r {vc} | isJust (dequeue vc dq)}
    -> {deliverable (fst (fromJust (dequeue vc dq))) vc}
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
deliverImpliesDeliverable
    :: {p:P r | isJust (internalDeliver p)}
    -> {deliverable (fst (fromJust (internalDeliver p))) (pVC p)}
@-}
deliverImpliesDeliverable :: P r -> Proof
deliverImpliesDeliverable p =
    case dequeue (pVC p) (pDQ p) of
        Nothing ->                              impossible
            {-restate premise-}             $   internalDeliver p
            {-by def of internalDeliver-}   === Nothing
        Just (m, pDQ') ->
            {-restate premise-}                 internalDeliver p
            {-by def of internalDeliver-}   === Just (m, p
                                                { pVC = vcCombine (mVC m) (pVC p)
                                                , pDQ = pDQ'
                                                , pHist = Deliver (pID p) (coerce m) : pHist p
                                                    `proofConst` internalDeliverCHA m (pID p) (pVC p) (pHist p) -- CHA_MIGRATION
                                                })
            ? dequeueImpliesDeliverable (pVC p) (pDQ p)
                                            *** QED

{-@
deliverPLCDpres_lemma1
    :: n:Nat
    -> p:Psized r {n}
    -> ClockHistoryAgreement {p}
    -> PLCD r {p}
    -> {p':Psized r {n} | isJust (internalDeliver p)
                        && p' == snd (fromJust (internalDeliver p)) }
    -> {m1:Msized r {n} | listElem (Deliver (pID p') m1) (pHist p')
                        && m1 == fst (fromJust (internalDeliver p)) }
    -> {m2:Msized r {n} | listElem (Deliver (pID p') m2) (pHist p')
                        && vcLess (mVC m1) (mVC m2) }
    -> { processOrder (pHist p') (Deliver (pID p') m1) (Deliver (pID p') m2) }
@-}
deliverPLCDpres_lemma1 :: Eq r => Int -> P r -> Proof -> (M r -> M r -> Proof) -> P r -> M r -> M r -> Proof
deliverPLCDpres_lemma1 n p pCHA _pPLCD p' m₁ m₂ =
    let
    e₁  =   Deliver (pID p) (coerce m₁)
    e₂  =   Deliver (pID p) (coerce m₂)
    deliverBody
        =   internalDeliver p
        === case dequeue (pVC p) (pDQ p) of
              Just (m, pDQ') -> Just (m, p
                { pVC = vcCombine (mVC m) (pVC p)
                , pDQ = pDQ'
                , pHist = Deliver (pID p) (coerce m) : pHist p
                    `proofConst` internalDeliverCHA m (pID p) (pVC p) (pHist p) -- CHA_MIGRATION
                }) -- by def of internalDeliver
    e₂inTail =
        {-restate a premise-}           e₂ `listElem` pHist p'
        ? deliverBody               === (pHist p' == e₁ : pHist p)
        ? mVC m₁`vcLess`mVC m₂      === (e₂ /= e₁)
        ? tailElem e₂ e₁ (pHist p)  === e₂ `listElem` pHist p
    m₁lessEqualpVC =
                                            True
        ? (mVC m₁ `vcLess` mVC m₂)      === mVC m₁ `vcLessEqual` mVC m₂
                                        === mVC m₂ == mVC (eventMessage n e₂)
        ? e₂inTail ? histElemLessEqualHistVC n e₂ p
                                        === mVC (eventMessage n e₂) `vcLessEqual` pHistVC p
        ? pCHA                          === pHistVC p `vcLessEqual` pVC p
        ? vcLessEqualTransitive n (mVC m₁) (mVC (eventMessage n e₂)) (pHistVC p)
        ? vcLessEqualTransitive n (mVC m₁) (pHistVC p) (pVC p)
                                        === mVC m₁ `vcLessEqual` pVC p
                                        *** QED
    m₁notLessEqualpVC =
                                            True
        ? deliverImpliesDeliverable p   === deliverable m₁ (pVC p)
        ? deliverableImpliesNotVCLessEqual m₁ (pVC p)
                                        === not (mVC m₁ `vcLessEqual` pVC p)
                                        *** QED
    in
    impossible  $   m₁lessEqualpVC
                &&& m₁notLessEqualpVC

{-@
deliverPLCDpres_lemma2
    :: n:Nat
    -> p:Psized r {n}
    -> ClockHistoryAgreement {p}
    -> PLCD r {p}
    -> {p':Psized r {n} | isJust (internalDeliver p)
                        && p' == snd (fromJust (internalDeliver p)) }
    -> {m1:Msized r {n} | listElem (Deliver (pID p') m1) (pHist p') }
    -> {m2:Msized r {n} | listElem (Deliver (pID p') m2) (pHist p')
                        && vcLess (mVC m1) (mVC m2)
                        && m2 == fst (fromJust (internalDeliver p)) }
    -> { processOrder (pHist p') (Deliver (pID p') m1) (Deliver (pID p') m2) }
@-}
deliverPLCDpres_lemma2 :: Eq r => Int -> P r -> Proof -> (M r -> M r -> Proof) -> P r -> M r -> M r -> Proof
deliverPLCDpres_lemma2 _n p _pCHA _pPLCD p' m₁ m₂ =
    let
    -- TODO: See if we can remove the non-coerce events?
    e₁  =   Deliver (pID p) m₁
        === Deliver (pID p) (coerce m₁)
    e₂  =   Deliver (pID p) m₂
        === Deliver (pID p) (coerce m₂)
    deliverBody
        =   internalDeliver p
        === case dequeue (pVC p) (pDQ p) of
              Just (m, pDQ') -> Just (m, p
                { pVC = vcCombine (mVC m) (pVC p)
                , pDQ = pDQ'
                , pHist = Deliver (pID p) (coerce m) : pHist p
                    `proofConst` internalDeliverCHA m (pID p) (pVC p) (pHist p) -- CHA_MIGRATION
                }) -- by def of internalDeliver
    p'Hist
        =   pHist p' ? deliverBody
        === e₂ : pHist p
    e₁inTail =
        {-restate a premise-}       e₁ `listElem` pHist p'
        ? p'Hist                === e₁ `listElem` (e₂ : pHist p)
        {-by def of listElem-}  === (e₁==e₂ || e₁ `listElem` pHist p)
        ? mVC m₁`vcLess`mVC m₂  === e₁ `listElem` pHist p
    in
                                True
    ? e₁inTail                  === e₁ `listElem` listTailForHead e₂ (pHist p')
    {-by def of processOrder-}  === processOrder (pHist p') e₁ e₂
                                *** QED

{-@
deliverPLCDpres_lemma3
    :: n:Nat
    -> p:Psized r {n}
    -> ClockHistoryAgreement {p}
    -> PLCD r {p}
    -> {p':Psized r {n} | isJust (internalDeliver p)
                        && p' == snd (fromJust (internalDeliver p)) }
    -> {m1:M r          | listElem (Deliver (pID p') m1) (pHist p') }
    -> {m2:MasM r {m1}  | listElem (Deliver (pID p') m2) (pHist p')
                        && vcLess (mVC m1) (mVC m2) }
    -> { m:Msized r {n} | m == fst (fromJust (internalDeliver p))
                        && m /= m1
                        && m /= m2 }
    -> { processOrder (pHist p') (Deliver (pID p') m1) (Deliver (pID p') m2) }
@-}
deliverPLCDpres_lemma3 :: Eq r => Int -> P r -> Proof -> (M r -> M r -> Proof) -> P r -> M r -> M r -> M r -> Proof
deliverPLCDpres_lemma3 _n p _pCHA pPLCD p' m₁ m₂ m =
    let
    -- TODO: See if we can remove the non-coerce events?
    e₁  =   Deliver (pID p) m₁
        === Deliver (pID p) (coerce m₁)
    e₂  =   Deliver (pID p) m₂
        === Deliver (pID p) (coerce m₂)
    e₃  =   Deliver (pID p) m
        === Deliver (pID p) (coerce m)
    deliverBody
        =   internalDeliver p
        === case dequeue (pVC p) (pDQ p) of
              Just (m', pDQ') -> Just (m', p
                { pVC = vcCombine (mVC m') (pVC p)
                , pDQ = pDQ'
                , pHist = Deliver (pID p) (coerce m') : pHist p
                    `proofConst` internalDeliverCHA m' (pID p) (pVC p) (pHist p) -- CHA_MIGRATION
                }) -- by def of internalDeliver
    p'Hist
        =   pHist p' ? deliverBody
        === e₃ : pHist p
    e₁inTail = -- TODO: use UCausalDelivery_CHA.tailElem
        {-restate a premise-}       e₁ `listElem` pHist p'
        ? p'Hist                === e₁ `listElem` (e₃ : pHist p)
        {-by def of listElem-}  === (e₁==e₃ || e₁ `listElem` pHist p)
        ? m₁ /= m               === e₁ `listElem` pHist p
    e₂inTail = -- TODO: use UCausalDelivery_CHA.tailElem
        {-restate a premise-}       e₂ `listElem` pHist p'
        ? p'Hist                === e₂ `listElem` (e₃ : pHist p)
        {-by def of listElem-}  === (e₂==e₃ || e₂ `listElem` pHist p)
        ? m₂ /= m               === e₂ `listElem` pHist p
    in
                                                True
    ? e₁inTail ? e₂inTail ? pPLCD m₁ m₂     === processOrder (pHist p) e₁ e₂
    ? extendProcessOrder (pHist p) e₁ e₂ e₃ === processOrder (e₃:pHist p) e₁ e₂
    ? p'Hist                                === processOrder (pHist p') e₁ e₂
                                            *** QED

{-@ ple deliverPLCDpres @-}
{-@
deliverPLCDpres :: n:Nat -> PLCDpreservation r {n} {deliverShim} @-}
deliverPLCDpres :: Eq r => Int -> P r -> (M r -> M r -> Proof) -> M r -> M r -> Proof
deliverPLCDpres n p pPLCD m₁ m₂ =
    let pCHA = bridgeCHA2 p in -- CHA_MIGRATION
    case dequeue (pVC p) (pDQ p) of -- by cases of internalDeliver
        Nothing -> pPLCD m₁ m₂ -- p is unchanged
----    Nothing -> -- p is unchanged
----        let p' = deliverShim p in
----            True
----        === Deliver (pID p') m₁ `listElem` pHist p' -- restate a premise
----        === Deliver (pID p') m₂ `listElem` pHist p' -- restate a premise
----        === mVC m₁ `vcLess` mVC m₂ -- restate a premise
----            ? (pID p' === pID p)
----            ? (pHist p' === pHist p)
----        === Deliver (pID p) m₁ `listElem` pHist p -- establish precond of pPLCD
----        === Deliver (pID p) m₂ `listElem` pHist p -- establish precond of pPLCD
----            ? pPLCD m₁ m₂
----        *** QED
        Just (m, _pDQ') -- p delivered m and became (deliverShim p)
            | m == m₁            -> deliverPLCDpres_lemma1 n p pCHA pPLCD (deliverShim p) m₁ m₂
            | m == m₂            -> deliverPLCDpres_lemma2 n p pCHA pPLCD (deliverShim p) m₁ m₂
            | m /= m₁ && m /= m₂ -> deliverPLCDpres_lemma3 n p pCHA pPLCD (deliverShim p) m₁ m₂ m
