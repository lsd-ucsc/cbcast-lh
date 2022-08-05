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

-- | An operation OP preserves any execution's observation of CD.
{-@
type CDpreservation r N OP
    =  x:Xsized r {N}
    -> CausalDelivery r {N} {x}
    -> CausalDelivery r {N} {OP x}
@-}

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

-- {-@ ple trcCDpres @-}
{-@
trcCDpres
  ::   n : Nat
  -> ops : [(OPsized r {n}, PIDsized {n})]
  -> CDpreservation r {n} {foldr_xStep_flip n ops}
@-}
trcCDpres :: Eq r => Int -> [(Op r, PID)] -> Execution r -> (PID -> Message r -> Message r -> Proof)
                                                         -> (PID -> Message r -> Message r -> Proof)
trcCDpres n [] x xCD {-λ-} p_id m₁ m₂ =
        foldr_xStep_flip n [] x        p_id
    === foldr_xStep n x []             p_id
    === foldr (uncurry (xStep n)) x [] p_id
    ==! x                              p_id -- QQQ why is PLE necessary for this step?
--      ? xCD p_id m₁ m₂
    *** Admit
trcCDpres n ((op, op_p_id):rest) x xCD {-λ-} p_id m₁ m₂ =
    () *** Admit
--  let
--      prev = foldr_xStep_flip n rest x
--      prevCD = trcCDpres n rest x xCD
--  in
--      xStepCDpres n op op_p_id prev prevCD
--      p_id m₁ m₂
--      *** Admit
