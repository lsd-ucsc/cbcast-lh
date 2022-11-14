{-# OPTIONS_GHC "-Wno-unused-imports" #-} -- LH needs bodies of reflected definitions
{-# OPTIONS_GHC "-Wno-warnings-deprecations" #-} -- Hide the "verification only" and "internal use" warnings

module CBCAST.Verification.Global.CDpresXStep {-# WARNING "Verification only" #-} where

import Language.Haskell.Liquid.ProofCombinators

import Redefined
import Redefined.Verification
import VectorClock
import CBCAST.Core
import CBCAST.Transitions
import CBCAST.Step
import CBCAST.Verification.ProcessOrder
import CBCAST.Verification.PLCDpresStep
import CBCAST.Verification.Shims
import CBCAST.Verification.Global.Core
import CBCAST.Verification.Global.XStep
import CBCAST.Verification.Global.PLCDpresXStep

-- | A function preserves any execution's observation of CD.
{-@
type CDpreservation r N F
    =  x:Xsized r {N}
    -> CausalDelivery r {N} {x}
    -> CausalDelivery r {N} {F x}
@-}

-- | Causal delivery is preserved by 'xStep'.
{-@
xStepCDpres :: n:Nat -> op:OPsized r {n} -> op_p_id:PIDsized {n} -> CDpreservation r {n} {xStep n op op_p_id} @-}
xStepCDpres :: Eq r => Int -> Op r -> PID -> Execution r -> (PID -> Message r -> Message r -> Proof)
                                                         -> (PID -> Message r -> Message r -> Proof)
xStepCDpres n op op_p_id x xCD = -- \ p_id m₁ m₂ ->
    let
    x' = xStep n op op_p_id x -- restate transition, then step x
    xPLCD = cdToPLCD n x xCD
    x'PLCD = xStepPLCDpres n op op_p_id x xPLCD
    x'CD = plcdToCD n x' x'PLCD
    in
    x'CD

-- | Causal delivery is preserved by multiple applications of 'xStep'.
{-@
trcCDpres
    ::   n : Nat
    -> ops : [(OPsized r {n}, PIDsized {n})]
    -> CDpreservation r {n} {funFlip' (listFoldr (funUncurry' (xStep n))) ops}
    / [len ops]
@-}
trcCDpres :: Eq r => Int -> [(Op r, PID)] -> Execution r -> (PID -> Message r -> Message r -> Proof)
                                                         -> (PID -> Message r -> Message r -> Proof)
trcCDpres n ((op, op_p_id):rest) xFirst xFirstCD {-λ-} p_id m₁ m₂ =
    let
        xPenult = funFlip' (listFoldr (funUncurry' (xStep n)))                rest  xFirst
        xLast   = funFlip' (listFoldr (funUncurry' (xStep n))) ((op, op_p_id):rest) xFirst -- restate part of conclusion
        xPenultCD = trcCDpres n rest xFirst xFirstCD -- inductive assumption
        xLastCD   = xStepCDpres n op op_p_id xPenult xPenultCD
    in
        trcCDpresInductiveCaseLemma (xStep n) (op, op_p_id) rest xFirst xPenult xLast
    &&& xLastCD p_id m₁ m₂
trcCDpres n [] xFirst xFirstCD {-λ-} p_id m₁ m₂ =
        trcCDpresBaseCaseLemma (xStep n) xFirst
    &&& xFirstCD p_id m₁ m₂

{-@
trcCDpresInductiveCaseLemma
    ::        f : (a1 -> a2 -> b -> b)
    ->        v :  (a1, a2)
    ->       vs : [(a1, a2)]
    ->    first :  b
    -> { penult :  b  | penult == listFoldr (funUncurry' f) first         vs  }
    -> {   last :  b  |   last == listFoldr (funUncurry' f) first (cons v vs) }
    -> { f (fst v) (snd v) penult == last }
@-}
trcCDpresInductiveCaseLemma :: (a1 -> a2 -> b -> b) -> (a1, a2) -> [(a1, a2)] -> b -> b -> b -> Proof
trcCDpresInductiveCaseLemma f v vs first penult last_ =
        listFoldrPenultimate (funUncurry' f) v vs first penult last_
    &&& funUncurry'Apply f v -- QQQ: INLINE THIS?

{-@
trcCDpresBaseCaseLemma
    ::     f : (a1 -> a2 -> b -> b)
    -> first : b
    -> { first == funFlip' (listFoldr (funUncurry' f)) [] first }
@-}
trcCDpresBaseCaseLemma :: (a1 -> a2 -> b -> b) -> b -> Proof
trcCDpresBaseCaseLemma f first =
        listFoldrEmpty (funUncurry' f) first -- QQQ: INLINE THIS?
    &&& funFlip'Apply (listFoldr (funUncurry' f)) [] first -- QQQ: INLINE THIS?
