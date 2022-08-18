{-# OPTIONS_GHC "-Wno-unused-imports" #-} -- LH needs bodies of reflected definitions
{-# OPTIONS_GHC "-Wno-warnings-deprecations" #-} -- Hide the "verification only" and "internal use" warnings

module CBCAST.Verification.Global.CDpresXStep {-# WARNING "Verification only" #-} where

import Prelude hiding (foldr, uncurry)
import Language.Haskell.Liquid.ProofCombinators

import Redefined
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

-- | An function preserves any execution's observation of CD.
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

{-@
trcCDpresBaseCaseLemma
    :: f : (Nat -> op -> pid -> ex -> ex)
    -> n : Nat
    -> x : ex
    -> { flip' (foldr (uncurry (f n))) [] x == x}
@-}
trcCDpresBaseCaseLemma :: (Int -> op -> pid -> ex -> ex) -> Int -> ex -> Proof
trcCDpresBaseCaseLemma f n x =
        flip' (foldr (uncurry (f n))) [] x -- restate part of concl
    ===        foldr (uncurry (f n))  x [] -- by body of flip'
    ===                               x    -- by body of foldr
    *** QED

-- | Causal delivery is preserved by multiple applications of 'xStep'.
{-@
trcCDpres
    ::   n : Nat
    -> ops : [(OPsized r {n}, PIDsized {n})]
    -> CDpreservation r {n} {flip' (foldr (uncurry (xStep n))) ops}
    / [len ops]
@-}
trcCDpres :: Eq r => Int -> [(Op r, PID)] -> Execution r -> (PID -> Message r -> Message r -> Proof)
                                                         -> (PID -> Message r -> Message r -> Proof)
trcCDpres n [] x xCD {-λ-} p_id m₁ m₂ =
        trcCDpresBaseCaseLemma xStep n x
    &&& xCD p_id m₁ m₂
trcCDpres n ((op, op_p_id):rest) x xCD {-λ-} p_id m₁ m₂ =
    let
        prev = flip' (foldr (uncurry (xStep n))) rest x
        prevCD = trcCDpres n rest x xCD
        last = flip' (foldr (uncurry (xStep n))) ((op, op_p_id):rest) x
            ==! xStep n op op_p_id prev
        lastCD = xStepCDpres n op op_p_id prev prevCD
    in
        lastCD p_id m₁ m₂
        ? last
