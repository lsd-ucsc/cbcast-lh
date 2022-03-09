{-# OPTIONS_GHC "-Wno-unused-imports" #-} -- LH needs bodies of reflected definitions

-- Proof that step preserves PLCD.
module MessagePassingAlgorithm.CBCAST.Verification.PLCD.Step where

import Language.Haskell.Liquid.ProofCombinators

import Redefined
import VectorClock
import MessagePassingAlgorithm.VectorClockAdapter
import MessagePassingAlgorithm.CBCAST
import MessagePassingAlgorithm.CBCAST.Interpreter

import MessagePassingAlgorithm.VectorClockAdapter.Verification.ProcessLocalCausalDelivery
import MessagePassingAlgorithm.CBCAST.Verification.ClockHistoryAgreement
import MessagePassingAlgorithm.CBCAST.Verification.ClockHistoryAgreementProofs
import MessagePassingAlgorithm.CBCAST.Verification.PLCD
import MessagePassingAlgorithm.CBCAST.Verification.PLCD.Receive
import MessagePassingAlgorithm.CBCAST.Verification.PLCD.Deliver
import MessagePassingAlgorithm.CBCAST.Verification.PLCD.Broadcast

{-@ type PasI r I = Psized r {inputSize I} @-}

-- | The step function but it ignores the process in the Input and takes a new
-- process one step and drops the Output.
{-@ stepShim :: i:Input r -> PasI r {i} -> PasI r {i} @-}
stepShim :: Input r -> P r -> P r
stepShim (InputReceive   n m _) p0 = case step (InputReceive   n m p0) of OutputReceive _ p             -> p
stepShim (InputBroadcast n r _) p0 = case step (InputBroadcast n r p0) of OutputBroadcast _ (_, p)      -> p
stepShim (InputDeliver   n   _) p0 = case step (InputDeliver   n   p0) of OutputDeliver _ (Just (_, p)) -> p
                                                                          OutputDeliver _ Nothing       -> p0
{-@ inline stepShim @-}

{-@
stepCHApres :: i:Input r -> CHApreservation r {inputSize i} {stepShim i} @-}
stepCHApres :: Input r -> P r -> Proof -> Proof
stepCHApres (InputReceive n m _pIGNORED) p pCHA =
    {-by def of stepShim-}              step (InputReceive n m p)
    {-by def of step-}              === OutputReceive n (internalReceive m p)
    ? receiveCHApres m p pCHA       *** QED
stepCHApres (InputBroadcast n r _pIGNORED) p pCHA =
    {-by def of stepShim-}              step (InputBroadcast n r p)
    {-by def of step-}              === OutputBroadcast n (internalBroadcast r p)
    ? broadcastCHApres r n p pCHA   *** QED
stepCHApres (InputDeliver n _pIGNORED) p pCHA =
    {-by def of stepShim-}              step (InputDeliver n p)
    {-by def of step-}              === OutputDeliver n (internalDeliver p)
    ? deliverCHApres n p pCHA       *** QED
