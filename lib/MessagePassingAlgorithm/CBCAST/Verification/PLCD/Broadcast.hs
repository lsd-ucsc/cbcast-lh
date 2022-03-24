{-# OPTIONS_GHC "-Wno-unused-imports" #-} -- LH needs bodies of reflected definitions

-- Proof that broadcast preserves PLCD.
module MessagePassingAlgorithm.CBCAST.Verification.PLCD.Broadcast where

import Language.Haskell.Liquid.ProofCombinators
import Language.Haskell.Liquid.ProofCombinatorsExtra

import Redefined
import VectorClock
import MessagePassingAlgorithm
import MessagePassingAlgorithm.CBCAST
import MessagePassingAlgorithm.VectorClockAdapter

import Redefined.Verification
import MessagePassingAlgorithm.VectorClockAdapter.Verification.ProcessLocalCausalDelivery
import MessagePassingAlgorithm.CBCAST.Verification.Shims
import MessagePassingAlgorithm.CBCAST.Verification.ClockHistoryAgreement
import MessagePassingAlgorithm.CBCAST.Verification.PLCD.Deliver

{-@
broadcastPrepareInjectPLCDpres :: raw:r -> n:Nat -> PLCDpreservation r {n} {broadcastPrepareInjectShim raw} @-}
broadcastPrepareInjectPLCDpres :: Eq r => r -> Int -> P r -> (M r -> M r -> Proof) -> M r -> M r -> Proof
broadcastPrepareInjectPLCDpres raw _n p pPLCD m₁ m₂ =
    let _pCHA = bridgeCHA2 p in -- CHA_MIGRATION
    let
    m = broadcastHelper_prepareMessage raw p
    p' = broadcastHelper_injectMessage m p
    e₁ = Deliver (pID p) (coerce m₁)
    e₂ = Deliver (pID p) (coerce m₂)
    e₃ = Broadcast (coerce m)
    injectMessageBody
        =   broadcastHelper_injectMessage m p
        === p { pDQ = m : pDQ p
              , pHist = Broadcast (coerce m) : pHist p
                  `proofConst` internalBroadcastCHA m (pVC p) (pHist p) -- CHA_MIGRATION
              }
    pIDLemma
                            =   pID p'
        ? injectMessageBody === pID p
    pHistLemma
                            =   pHist p'
        ? injectMessageBody === e₃ : pHist p
    in
                                            True
    ? pIDLemma
    ? tailElem e₁ e₃ (pHist p)
    ? tailElem e₂ e₃ (pHist p)
    ? pPLCD m₁ m₂
                                            === processOrder (pHist p) e₁ e₂
    ? extendProcessOrder (pHist p) e₁ e₂ e₃ === processOrder (e₃ : pHist p) e₁ e₂
    ? pHistLemma                            === processOrder (pHist p') e₁ e₂
    *** QED

{-@
broadcastPLCDpres :: raw:r -> n:Nat -> PLCDpreservation r {n} {broadcastShim raw} @-}
broadcastPLCDpres :: Eq r => r -> Int -> P r -> (M r -> M r -> Proof) -> M r -> M r -> Proof
broadcastPLCDpres raw n p pPLCD = -- ∀ m m'
    let
    p' = broadcastPrepareInjectShim raw p
    p'' = broadcastShim raw p

    -- relate p and p' and p''
    broadcastBody                                   =   p''
    --  {-by def of p''-}                           === broadcastShim raw p
        {-by def of broadcastShim-}                 === (let (_m, _p) = internalBroadcast raw p in _p)
        ? broadcastAlwaysDelivers raw p
    --  {-by def of internalBroadcast-}             === (let _m = broadcastHelper_prepareMessage raw p
    --                                                       _p = broadcastHelper_injectMessage _m p
    --                                                       Just (__m, __p) = internalDeliver _p in __p)
    --  {-by composition of functions-}             === (let _p = broadcastHelper_injectMessage (broadcastHelper_prepareMessage raw p) p
    --                                                       Just (__m, __p) = internalDeliver _p in __p)
    --  {-by def of broadcastPrepareInjectShim-}    === (let _p = broadcastPrepareInjectShim raw p
    --                                                       Just (__m, __p) = internalDeliver _p in __p)
        {-by def of p'-}                            === (let Just (__m, __p) = internalDeliver p' in __p)

--  in
--  deliverPLCDpres n p' -- p'PLCD to p''PLCD
--      (broadcastPrepareInjectCHApres raw n p pCHA) -- pCHA to p'CHA
--      (broadcastPrepareInjectPLCDpres raw n p pCHA pPLCD) -- pPLCD to p'PLCD
--      ? broadcastBody
--      -- ∀ m m'

    -- convert evidence from p to p'
    p'PLCD = broadcastPrepareInjectPLCDpres raw n p pPLCD -- ∀ m m'
        ? bridgeCHA2 p -- CHA_MIGRATION
    -- convert evidence from p' to p''
    p''PLCD = deliverPLCDpres n p' p'PLCD -- ∀ m m'
        ? bridgeCHA2 p' -- CHA_MIGRATION
    in
    (p''PLCD ? broadcastBody) -- ∀ m m'
