{-# OPTIONS_GHC "-Wno-unused-imports" #-} -- LH needs bodies of reflected definitions

-- Proof that step preserves PLCD.
module MessagePassingAlgorithm.CBCAST.Step.Verification where

import Language.Haskell.Liquid.ProofCombinators

import Redefined
import VectorClock
import MessagePassingAlgorithm.VectorClockAdapter
import MessagePassingAlgorithm.CBCAST
import MessagePassingAlgorithm.CBCAST.Step

import MessagePassingAlgorithm.VectorClockAdapter.Verification.ProcessLocalCausalDelivery
import MessagePassingAlgorithm.CBCAST.Verification.ClockHistoryAgreement
import MessagePassingAlgorithm.CBCAST.Verification.ClockHistoryAgreementProofs
import MessagePassingAlgorithm.CBCAST.Verification.PLCD
import MessagePassingAlgorithm.CBCAST.Verification.PLCD.Receive
import MessagePassingAlgorithm.CBCAST.Verification.PLCD.Deliver
import MessagePassingAlgorithm.CBCAST.Verification.PLCD.Broadcast

-- | The step function but drops the output.
{-@ stepShim :: i:Input r -> PasI r {i} -> PasI r {i} @-}
stepShim :: Input r -> P r -> P r
stepShim i p₀ = case step i p₀ of
    OutputReceive _ p             -> p
    OutputBroadcast _ (_, p)      -> p
    OutputDeliver _ (Just (_, p)) -> p
    OutputDeliver _ Nothing       -> p₀
{-@ inline stepShim @-}

{-@
stepCHApres :: i:Input r -> CHApreservation r {inputSize i} {stepShim i} @-}
stepCHApres :: Input r -> P r -> Proof -> Proof
stepCHApres i p pCHA =
  case i of
    InputReceive   n m -> receiveCHApres   m   p pCHA ? (step i p === OutputReceive   n (internalReceive   m p))
    InputDeliver   n   -> deliverCHApres     n p pCHA ? (step i p === OutputDeliver   n (internalDeliver     p))
    InputBroadcast n r -> broadcastCHApres r n p pCHA ? (step i p === OutputBroadcast n (internalBroadcast r p))

{-@
stepPLCDpres :: i:Input r -> PLCDpreservation' r {inputSize i} {stepShim i} @-}
stepPLCDpres :: Eq r => Input r -> P r -> Proof -> (M r -> M r -> Proof) -> M r -> M r -> Proof
stepPLCDpres i p pCHA pPLCD = -- ∀ m m'
  case i of
    InputReceive   n m -> receivePLCDpres   m   p      pPLCD ? (step i p === OutputReceive   n (internalReceive   m p))
    InputDeliver   n   -> deliverPLCDpres     n p pCHA pPLCD ? (step i p === OutputDeliver   n (internalDeliver     p))
    InputBroadcast n r -> broadcastPLCDpres r n p pCHA pPLCD ? (step i p === OutputBroadcast n (internalBroadcast r p))
