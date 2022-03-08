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

-- | The step function but ignoring output.
{-@ stepShim :: i:Input r -> PasI r {i} -> PasI r {i} @-}
stepShim :: Input r -> P r -> P r
stepShim i p =
    let (_, p') = step i p in p'
{-@ inline stepShim @-}

{-@
stepCHApres :: i:Input r -> CHApreservation r {inputSize i} {stepShim i} @-}
stepCHApres :: Input r -> P r -> Proof -> Proof
stepCHApres input p pCHA =
    case input of
        InputReceive n m ->
                step input p
            === (OutputReceive n, internalReceive m p)
                ? receiveCHApres m p pCHA
            *** QED
        InputBroadcast n r ->
            let (m, p') = internalBroadcast r p in
                step input p
            === (OutputBroadcast n m, p')
                ? broadcastCHApres r n p pCHA
            *** QED
        InputDeliver n ->
            case internalDeliver p of
                Nothing ->
                        step input p
                    === (OutputDeliver n Nothing, p)
                        ? deliverCHApres n p pCHA
                    *** QED
                Just (m, p') ->
                        step input p
                    === (OutputDeliver n (Just m), p')
                        ? deliverCHApres n p pCHA
                    *** QED
