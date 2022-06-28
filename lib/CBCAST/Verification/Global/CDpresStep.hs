{-# OPTIONS_GHC "-Wno-unused-imports" #-} -- LH needs bodies of reflected definitions
{-# OPTIONS_GHC "-Wno-warnings-deprecations" #-} -- Hide the "verification only" and "internal use" warnings

module CBCAST.Verification.Global.CDpresStep {-# WARNING "Verification only" #-} where

import Language.Haskell.Liquid.ProofCombinators

import Redefined
import CBCAST.Core
import CBCAST.Step
import CBCAST.Verification.ProcessOrder
import CBCAST.Verification.Global.Core
import CBCAST.Verification.Global.Step

-- | An operation OP preserves any execution's observation of CD.
{-@
type CDpreservation r N OP
    =  x:Xsized r {N}
    -> CausalDelivery r {N} {x}
    -> CausalDelivery r {N} {OP x}
@-}

{-@
xStepCDpres :: n:Nat -> op:OPsized r {n} -> p_id:PIDsized {n} -> CDpreservation r {n} {xStep n op p_id} @-}
xStepCDpres :: Int -> Op r -> PID -> Execution r -> (PID -> Message r -> Message r -> Proof)
                                                 -> (PID -> Message r -> Message r -> Proof)
xStepCDpres _n _op _op_p_id _x _xCD =
  \ _p_id _m₁ _m₂ -> () *** Admit -- TODO
