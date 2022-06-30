{-# OPTIONS_GHC "-Wno-unused-imports" #-} -- LH needs bodies of reflected definitions
{-# OPTIONS_GHC "-Wno-warnings-deprecations" #-} -- Hide the "verification only" and "internal use" warnings

module CBCAST.Verification.Global.PLCDpresXStep {-# WARNING "Verification only" #-} where

import Language.Haskell.Liquid.ProofCombinators

import Redefined
import VectorClock
import CBCAST.Core
import CBCAST.Step
import CBCAST.Verification.ProcessOrder
import CBCAST.Verification.PLCD
import CBCAST.Verification.PLCDpresStep
import CBCAST.Verification.PIDpresStep
import CBCAST.Verification.Global.Core
import CBCAST.Verification.Global.Step

{-@ LIQUID "--skip-module" @-}

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
xStepPLCDpres n op op_p_id x xPLCD p_id m₁ m₂
  | op_p_id == p_id =
    let
    -- global to local, local step
    p = x p_id
    p' = stepShim op p
    -- global to local, local step
    pPLCD = xPLCD p_id
    p'PLCD = stepPLCDpres op p pPLCD
    -- prove that (x' p_id) is p' and then use p'PLCD to complete proof
    pIsUpdated
        {-restate concl-}               =   xStep       n op op_p_id  x p_id
        {-def of xStep-}                === xSetProc    n          p' x p_id
        {-def of xSetProc-}             === xSetPidProc n (pID p') p' x p_id
        ? stepPIDpres n op (x op_p_id)  === xSetPidProc n  op_p_id p' x p_id
        {-def of xSetPidProc-}          === (if p_id == op_p_id then p' else x p_id)
        {-op_p_id == p_id-}             === p'
    in
    ()
        ? pIsUpdated
        ? p'PLCD m₁ m₂
  | otherwise =
    let
    -- prove that (x' p_id) is (x p_id) and use xPLCD to complete proof
    op_p' = stepShim op (x op_p_id)
    pNotUpdated
        {-restate concl-}               =   xStep       n op op_p_id        x p_id
        {-def of xStep-}                === xSetProc    n             op_p' x p_id
        {-def of xSetProc-}             === xSetPidProc n (pID op_p') op_p' x p_id
        ? stepPIDpres n op (x op_p_id)  === xSetPidProc n  op_p_id    op_p' x p_id
        {-def of xSetPidProc-}          === (if p_id == op_p_id then op_p' else x p_id)
        ? (True === p_id /= op_p_id)    === x p_id
    in
    ()
        ? pNotUpdated
        ? xPLCD p_id m₁ m₂
