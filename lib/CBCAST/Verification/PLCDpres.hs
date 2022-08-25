{-# OPTIONS_GHC "-Wno-unused-imports" #-} -- LH needs bodies of reflected definitions
{-# OPTIONS_GHC "-Wno-warnings-deprecations" #-} -- Hide the "verification only" and "internal use" warnings

module CBCAST.Verification.PLCDpres {-# WARNING "Verification only" #-} where

import Language.Haskell.Liquid.ProofCombinators (Proof, (===), (***), QED(..), (?))

import Redefined
import VectorClock
import CBCAST.Core
import CBCAST.Transitions
import CBCAST.Verification.ProcessOrder
import CBCAST.Verification.PLCD

-- | A function preserves any process' observation of PLCD.
{-@
type PLCDpreservation r N F
    =  p:Psized r {N}
    -> PLCD r {N} {p}
    -> PLCD r {N} {F p}
@-}




-- * PLCD preservation of Receive

-- | The receive transition preserves PLCD.
--
-- This proof is in this module because it exercises the definition of
-- PLCDpreservation and forces LH to resolve all the symbols.
{-@ ple receivePreservesIDandHist @-}
{-@
receivePreservesIDandHist :: m:Message r -> p:PasM r {m} -> { pID p == pID (internalReceive m p)
                                                     && pHist p == pHist (internalReceive m p) } @-}
receivePreservesIDandHist :: Message r -> Process r -> Proof
receivePreservesIDandHist m p -- by cases from receive
    | mSender m == pID p = ()
    | otherwise =
            internalReceive m p
        === p{ pDQ = enqueue m (pDQ p) }
        *** QED

{-@ ple receivePLCDpres @-}
{-@
receivePLCDpres :: m:Message r -> PLCDpreservation r {messageSize m} {internalReceive m} @-}
receivePLCDpres :: Eq r => Message r -> Process r -> (Message r -> Message r -> Proof) -> Message r -> Message r -> Proof
receivePLCDpres m p pPLCD m₁ m₂ =
    let p' = internalReceive m p
    in  True
    === Deliver (pID p') m₁ `listElem` pHist p' -- restate a premise
    === Deliver (pID p') m₂ `listElem` pHist p' -- restate a premise
    === mVC m₁ `vcLess` mVC m₂ -- restate a premise
        ? receivePreservesIDandHist m p
    === Deliver (pID p) m₁ `listElem` pHist p -- establish precond of pPLCD
    === Deliver (pID p) m₂ `listElem` pHist p -- establish precond of pPLCD
        ? pPLCD m₁ m₂ -- generate evidence
    === processOrder (pHist p) (Deliver (pID p) m₁) (Deliver (pID p) m₂) -- restate generated evidence
    === processOrder (pHist p') (Deliver (pID p') m₁) (Deliver (pID p') m₂) -- restate conclusion
    *** QED
    --- NOTE: can comment out all of the equivalences here

