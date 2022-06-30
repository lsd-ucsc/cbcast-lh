{-# OPTIONS_GHC "-Wno-unused-imports" #-} -- LH needs bodies of reflected definitions
{-# OPTIONS_GHC "-Wno-warnings-deprecations" #-} -- Hide the "verification only" and "internal use" warnings

module CBCAST.Verification.Global.PLCDpresXStep {-# WARNING "Verification only" #-} where

import Language.Haskell.Liquid.ProofCombinators

import Redefined
import VectorClock
import CBCAST.Core
import CBCAST.Step
import CBCAST.Verification.ProcessOrder
import CBCAST.Verification.Shims
import CBCAST.Verification.PLCD
import CBCAST.Verification.PLCDpresStep
import CBCAST.Verification.PIDpresStep
import CBCAST.Verification.Global.Core
import CBCAST.Verification.Global.Step

{-@
xStepPLCDpres
    :: n:Nat -> op:OPsized r {n} -> op_p_id:PIDsized {n} -> x:Xsized r {n}
    -> ( p_id:PIDsized {n} -> PLCD r {n}                    {x p_id} )
    -> ( p_id:PIDsized {n} -> PLCD r {n} {xStep n op op_p_id x p_id} )
@-}
xStepPLCDpres :: Eq r
    => Int -> Op r -> PID -> Execution r
    -> (PID -> Message r -> Message r -> Proof)
    -> (PID -> Message r -> Message r -> Proof)
xStepPLCDpres n op op_p_id x xPLCD {-x'PLCD λ-} p_id m₁ m₂
  | op_p_id == p_id =
    let
    -- global to local, local step
    p = x p_id
    pPLCD = xPLCD p_id
    p' = stepShim op p
    p'PLCD = stepPLCDpres op p pPLCD
    in -- prove that (x' p_id) is p' and then use p'PLCD to complete proof
                                                            (xStep n op op_p_id x) p_id
    ? stepPIDpres n op (x op_p_id) ? (p_id === pID p')
    ? xSettedProc n p' x p_id                           === p'
    ? p'PLCD m₁ m₂                                      *** QED
  | otherwise =
    let
    -- global to local, local step
    op_p = x op_p_id
    op_p' = stepShim op op_p
    in -- prove that (x' p_id) is (x p_id) and use xPLCD to complete proof
                                                                (xStep n op op_p_id x) p_id
    ? stepPIDpres n op op_p ? (True === p_id /= pID op_p')
    ? xSettedProc n op_p' x p_id                            === x p_id
    ? xPLCD p_id m₁ m₂                                      *** QED
