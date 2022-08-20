{-# OPTIONS_GHC "-Wno-unused-imports" #-} -- LH needs bodies of reflected definitions
{-# OPTIONS_GHC "-Wno-warnings-deprecations" #-} -- Hide the "verification only" and "internal use" warnings

module CBCAST.Verification.PLCDpresDeliver {-# WARNING "Verification only" #-} where

import Language.Haskell.Liquid.ProofCombinators (Proof, (===), (***), QED(..), (?), impossible, (&&&))
import Language.Haskell.Liquid.ProofCombinatorsExtra (proofConst)

import Redefined
import Redefined.Verification
import VectorClock
import VectorClock.Verification
import CBCAST.Core
import CBCAST.Transitions
import CBCAST.Step
import CBCAST.Verification.Core
import CBCAST.Verification.ProcessOrder
import CBCAST.Verification.Shims
import CBCAST.Verification.PLCD
import CBCAST.Verification.PLCDpres




-- * PLCD preservation of Deliver

-- | A message which is delivered by a process is a deliverable message at that
-- process.
{-@
deliverImpliesDeliverable
    :: {p:Process r | isJust (internalDeliver p)}
    -> {deliverable (fst (fromJust (internalDeliver p))) (pVC p)}
@-}
deliverImpliesDeliverable :: Process r -> Proof
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
                                                , pHist = Deliver (pID p) m : pHist p
                                                    `proofConst` internalDeliverCHA m (pID p) (pVC p) (pHist p)
                                                })
            ? dequeueImpliesDeliverable (pVC p) (pDQ p)
                                            *** QED

-- | m₁ is Delivered: Lemma showing a causal violation is not possible.
{-@
deliverPLCDpres_lemNoCausalViolation
    ::   n:Nat
    -> { p:Psized r {n} | isJust (internalDeliver p) }
    ->     PLCD r {n} {p}
    -> {p':Psized r {n} | p' == snd (fromJust (internalDeliver p)) }
    -> {m1:Msized r {n} | listElem (Deliver (pID p') m1) (pHist p')
                       && m1 == fst (fromJust (internalDeliver p)) }
    -> {m2:Msized r {n} | listElem (Deliver (pID p') m2) (pHist p')
                       && vcLess (mVC m1) (mVC m2) }
    -> { processOrder (pHist p') (Deliver (pID p') m1) (Deliver (pID p') m2) }
@-}
deliverPLCDpres_lemNoCausalViolation :: Eq r => Int -> Process r -> (Message r -> Message r -> Proof)
                                                    -> Process r -> (Message r -> Message r -> Proof)
deliverPLCDpres_lemNoCausalViolation n p _pPLCD p' m₁ m₂ =
    let
    e₁ = Deliver (pID p') m₁
    e₂ = Deliver (pID p') m₂
    pHistVC = histVC n (pHist p)
    deliverBody
        =   internalDeliver p
        === case dequeue (pVC p) (pDQ p) of
              Just (mₓ, pDQ') -> Just (mₓ, p
                { pVC = vcCombine (mVC mₓ) (pVC p)
                , pDQ = pDQ'
                , pHist = Deliver (pID p) mₓ : pHist p
                    `proofConst` internalDeliverCHA mₓ (pID p) (pVC p) (pHist p)
                }) -- by def of internalDeliver
    e₂inTail =
        (pHist p' ? deliverBody
            === e₁ : pHist p)
        ? (mVC m₁`vcLess`mVC m₂)
        ? tailElem e₂ e₁ (pHist p)
    -- mVC m₁ ≤ mVC m₂
    --          mVC m₂ ≡ eVC e₂
    --                   eVC e₂ ≤ histVC
    --                            histVC ≡ pVC p
    -- ⇒ mVC m₁ ≤ pVC p
    m₁lessEqualpVC =
                                        True
        ? (mVC m₁ `vcLess` mVC m₂)  === mVC m₁ `vcLessEqual` mVC m₂
                                    === mVC m₂ == mVC (eventMessage e₂)
        ? e₂inTail ? histElemLessEqualHistVC n e₂ (pHist p)
                                    === mVC (eventMessage e₂) `vcLessEqual` pHistVC
        {- CHA -}                   === pHistVC == pVC p
        ? vcLessEqualTransitive n (mVC m₁) (mVC m₂) (pVC p)
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

-- | m₂ is Delivered: Lemma showing a causally ordered delivery establishes process order.
{-@
deliverPLCDpres_lemM1thenM2
    ::   n:Nat
    -> { p:Psized r {n} | isJust (internalDeliver p) }
    ->     PLCD r {n} {p}
    -> {p':Psized r {n} | p' == snd (fromJust (internalDeliver p)) }
    -> {m1:Msized r {n} | listElem (Deliver (pID p') m1) (pHist p') }
    -> {m2:Msized r {n} | listElem (Deliver (pID p') m2) (pHist p')
                       && vcLess (mVC m1) (mVC m2)
                       && m2 == fst (fromJust (internalDeliver p)) }
    -> { processOrder (pHist p') (Deliver (pID p') m1) (Deliver (pID p') m2) }
@-}
deliverPLCDpres_lemM1thenM2 :: Eq r => Int -> Process r -> (Message r -> Message r -> Proof)
                                           -> Process r -> (Message r -> Message r -> Proof)
deliverPLCDpres_lemM1thenM2 _n p _pPLCD p' m₁ m₂ =
    let
    e₁ = Deliver (pID p') m₁
    e₂ = Deliver (pID p') m₂
    deliverBody
        =   internalDeliver p
        === case dequeue (pVC p) (pDQ p) of
              Just (mₓ, pDQ') -> Just (mₓ, p
                { pVC = vcCombine (mVC mₓ) (pVC p)
                , pDQ = pDQ'
                , pHist = Deliver (pID p) mₓ : pHist p
                    `proofConst` internalDeliverCHA mₓ (pID p) (pVC p) (pHist p)
                }) -- by def of internalDeliver
    in
                                    True
    ? (pHist p' ? deliverBody
        === e₂ : pHist p)
    ? (mVC m₁`vcLess`mVC m₂)
    ? tailElem e₁ e₂ (pHist p)  === e₁ `listElem` listTailForHead e₂ (pHist p')
    {-by def of processOrder-}  === processOrder (pHist p') e₁ e₂
                                *** QED

-- | mₙ is Delivered: Lemma showing a new delivery does not alter process order.
{-@
deliverPLCDpres_lemNewM
    ::   n:Nat
    -> { p:Psized r {n} | isJust (internalDeliver p) }
    ->     PLCD r {n} {p}
    -> {p':Psized r {n} | p' == snd (fromJust (internalDeliver p)) }
    -> {m1:Msized r {n} | listElem (Deliver (pID p') m1) (pHist p') }
    -> {m2:Msized r {n} | listElem (Deliver (pID p') m2) (pHist p')
                       && vcLess (mVC m1) (mVC m2) }
    -> { m:Msized r {n} | m == fst (fromJust (internalDeliver p))
                       && m /= m1
                       && m /= m2 }
    -> { processOrder (pHist p') (Deliver (pID p') m1) (Deliver (pID p') m2) }
@-}
deliverPLCDpres_lemNewM :: Eq r => Int -> Process r -> (Message r -> Message r -> Proof)
                                       -> Process r -> Message r -> Message r -> Message r -> Proof
deliverPLCDpres_lemNewM _n p pPLCD p' m₁ m₂ mₙ =
    let
    e₁ = Deliver (pID p') m₁
    e₂ = Deliver (pID p') m₂
    e₃ = Deliver (pID p ) mₙ
    deliverBody
        =   internalDeliver p
        === case dequeue (pVC p) (pDQ p) of
              Just (mₓ, pDQ') -> Just (mₓ, p
                { pVC = vcCombine (mVC mₓ) (pVC p)
                , pDQ = pDQ'
                , pHist = Deliver (pID p) mₓ : pHist p
                    `proofConst` internalDeliverCHA mₓ (pID p) (pVC p) (pHist p)
                }) -- by def of internalDeliver
    in
                                                True
    ? (pHist p' ? deliverBody
        === e₃ : pHist p)
    ? tailElem e₁ e₃ (pHist p)
    ? tailElem e₂ e₃ (pHist p)
    ? pPLCD m₁ m₂                           === processOrder (pHist p) e₁ e₂
    ? extendProcessOrder (pHist p) e₁ e₂ e₃ === processOrder (e₃:pHist p) e₁ e₂
                                            *** QED

-- | The deliver transition preserves PLCD.
{-@
deliverPLCDpres :: n:Nat -> PLCDpreservation r {n} {deliverShim} @-}
deliverPLCDpres :: Eq r => Int -> Process r -> (Message r -> Message r -> Proof)
                                            -> (Message r -> Message r -> Proof)
deliverPLCDpres n p pPLCD m₁ m₂ =
    case internalDeliver p of
        Nothing -> -- p is unchanged
            pPLCD m₁ m₂
        Just (mₙ, p') -- p delivered m and became (deliverShim p)
            | mₙ == m₁             -> deliverPLCDpres_lemNoCausalViolation n p pPLCD p' m₁ m₂
            | mₙ == m₂             -> deliverPLCDpres_lemM1thenM2          n p pPLCD p' m₁ m₂
            | mₙ /= m₁ && mₙ /= m₂ -> deliverPLCDpres_lemNewM              n p pPLCD p' m₁ m₂ mₙ
