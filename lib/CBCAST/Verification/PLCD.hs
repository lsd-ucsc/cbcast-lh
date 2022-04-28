{-# OPTIONS_GHC "-Wno-unused-imports" #-} -- LH needs bodies of reflected definitions
{-# OPTIONS_GHC "-Wno-warnings-deprecations" #-} -- Hide the "verification only" and "internal use" warnings

-- | Definition of process-local causal delivery for a CBCAST process.
module CBCAST.Verification.PLCD {-# WARNING "Verification only" #-} where

import Language.Haskell.Liquid.ProofCombinators (Proof, (===), (***), QED(..))
import Language.Haskell.Liquid.ProofCombinatorsExtra (proofConst)

import Redefined
import VectorClock
import CBCAST.Core
import CBCAST.Verification.ProcessOrder (processOrder)

-- | Process-Local Causal Delivery property
{-@
type PLCD r N PROC
    =  {m1 : Msized r {N} | listElem (Deliver (pID PROC) m1) (pHist PROC) }
    -> {m2 : Msized r {N} | listElem (Deliver (pID PROC) m2) (pHist PROC)
                && vcLess (mVC m1) (mVC m2) }
    -> {_ : Proof | processOrder (pHist PROC) (Deliver (pID PROC) m1) (Deliver (pID PROC) m2) }
@-}




-- | The empty CBCAST process observes PLCD.
--
-- This proof is in this module because it exercises the definition of PLCD and
-- forces LH to resolve all the symbols.
{-@ ple pEmptyPLCD @-}
{-@
pEmptyPLCD :: n:Nat -> p_id:PIDsized {n} -> PLCD r {n} {pEmpty n p_id} @-}
pEmptyPLCD :: Eq r => Int -> Fin -> (Message r -> Message r -> Proof)
pEmptyPLCD n p_id m1 _m2
    =   True
    --- QQQ: Why doesn't this premise report as True without PLE?
    === listElem (Deliver p_id m1) (pHist (pEmpty n p_id)) -- restate a premise
    --- QQQ: Why doesn't expanding the definition of pEmpty work without PLE?
    === listElem (Deliver p_id m1) (pHist Process{pVC=vcEmpty n, pID=p_id, pDQ=[], pHist=[]}) -- by def of pEmpty
    === listElem (Deliver p_id m1) [] -- by def of pHist
    === False -- by def of listElem
    *** QED -- premise failed
-- NOTE: can comment the proof above in favor of oneliner below.
-- pEmptyPLCD _n _p_id _m1 _m2 = () -- Premises don't hold.
