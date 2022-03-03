
-- Proof that receive preserves PLCD.
module UCausalDelivery_PLCDreceive where

import Language.Haskell.Liquid.ProofCombinators
import Redefined.Fin
import Redefined.Ord
import Redefined.Proof (proofConst)

import SystemModel
import Properties
import Properties2
import UCausalDelivery
import UCausalDelivery_PLCD

{-@ ple receivePreservesIDandHist @-}
{-@
receivePreservesIDandHist :: m:M r -> p:PasM r {m} -> { pID p == pID (internalReceive m p)
                                                     && pHist p == pHist (internalReceive m p) } @-}
receivePreservesIDandHist :: M r -> P r -> Proof
receivePreservesIDandHist m p -- by cases from receive
    | mSender m == pID p = ()
    | otherwise = ()

{-@ ple receivePLCDpres @-}
{-@
receivePLCDpres :: m:M r -> PLCDpreservation r {len (mVC m)} {internalReceive m} @-}
receivePLCDpres :: Eq r => M r -> P r -> (M r -> M r -> Proof) -> M r -> M r -> Proof
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
