{-# OPTIONS_GHC "-Wno-unused-imports" #-} -- LH needs bodies of reflected definitions

-- | Definition of process local causal delivery for a CBCAST process.
module MessagePassingAlgorithm.CBCAST.Verification.PLCD where

import Language.Haskell.Liquid.ProofCombinators
import Language.Haskell.Liquid.ProofCombinatorsExtra

import Redefined
import VectorClock
import MessagePassingAlgorithm
import MessagePassingAlgorithm.VectorClockAdapter
import MessagePassingAlgorithm.CBCAST

import MessagePassingAlgorithm.VectorClockAdapter.Verification.ProcessLocalCausalDelivery
import MessagePassingAlgorithm.CBCAST.Verification.ClockHistoryAgreement

-- | An alias for process local causal delivery in terms of the CBCAST process
-- type.
{-@
type PLCD r P
    = ProcessLocalCausalDelivery r {pID P} {pHist P}
@-}

{-@
type PLCDpreservation r N OP
    =  p:Psized r {N}
    -> PLCD r {p}
    -> PLCD r {OP p}
@-}

-- | The empty CBCAST process observes PLCD. This proof is in this module
-- because it exercises the definition of PLCD and forces LH to resolve all the
-- symbols.
{-@ ple pEmptyPLCD @-}
{-@
pEmptyPLCD :: n:Nat -> p_id:PIDsized {n} -> PLCD r {pEmpty n p_id} @-}
pEmptyPLCD :: Eq r => Int -> Fin -> (M r -> M r -> Proof)
-- pEmptyPLCD _n _p_id _m1 _m2 = () -- Premises don't hold.
-- NOTE: can comment the proof below
pEmptyPLCD n p_id m1 _m2
    =   True
    --- QQQ: Why doesn't this premise report as True without PLE?
    === listElem (Deliver p_id m1) (pHist (pEmpty n p_id)) -- restate a premise
    --- QQQ: Why doesn't expanding the definition of pEmpty work without PLE?
    === listElem (Deliver p_id m1) (pHist P{pVC=vcEmpty n, pID=p_id, pDQ=[], pHist=[]}) -- by def of pEmpty
    === listElem (Deliver p_id m1) [] -- by def of pHist
    === False -- by def of listElem
    *** QED -- premise failed
