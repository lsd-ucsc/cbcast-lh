{-# OPTIONS_GHC "-Wno-unused-imports" #-} -- LH needs bodies of reflected definitions
{-# OPTIONS_GHC "-Wno-warnings-deprecations" #-} -- Hide the "verification only" and "internal use" warnings

module CBCAST.Verification.Global.XStepPresCD {-# WARNING "Verification only" #-} where

import Language.Haskell.Liquid.ProofCombinators

import Redefined
import VectorClock
import CBCAST.Core
import CBCAST.Step
import CBCAST.Verification.ProcessOrder
import CBCAST.Verification.PLCDpresStep
import CBCAST.Verification.Global.Core
import CBCAST.Verification.Global.XStep
import CBCAST.Verification.Global.XStepPresPLCD

-- | An operation OP preserves any execution's observation of CD.
{-@
type CDpreservation r N OP
    =  x:Xsized r {N}
    -> CausalDelivery r {N} {x}
    -> CausalDelivery r {N} {OP x}
@-}

{-@
xStepPresCD :: n:Nat -> op:OPsized r {n} -> op_p_id:PIDsized {n} -> CDpreservation r {n} {xStep n op op_p_id} @-}
xStepPresCD :: Eq r => Int -> Op r -> PID -> Execution r -> (PID -> Message r -> Message r -> Proof)
                                                         -> (PID -> Message r -> Message r -> Proof)
xStepPresCD n op op_p_id x xCD = -- \ p_id m₁ m₂ ->
    let
    x' = xStep n op op_p_id x -- restate transition, then step x
    xPLCD = cdToPLCD n x xCD
    x'PLCD = xStepPresPLCD n op op_p_id x xPLCD
    x'CD = plcdToCD n x' x'PLCD
    in
    x'CD
