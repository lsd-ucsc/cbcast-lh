
-- Process local causal delivery definition.
module UCausalDelivery_PLCD where

import Language.Haskell.Liquid.ProofCombinators
import Redefined.Fin
import Redefined.Ord
import Redefined.Proof (proofConst)

import SystemModel
import Properties
import Properties2
import UCausalDelivery
import UCausalDelivery_CHA

-- An alias for the system model's PLCD in terms of the MPA's process type.
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

-- PLCD preservation with an extra CHA precondition.
{-@
type PLCDpreservation' r N OP
    =  p:Psized r {N}
    -> ClockHistoryAgreement {p}
    -> PLCD r {p}
    -> PLCD r {OP p}
@-}

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
