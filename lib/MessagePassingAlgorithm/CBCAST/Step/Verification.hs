{-# OPTIONS_GHC "-Wno-unused-imports" #-} -- LH needs bodies of reflected definitions

-- Proof that step preserves PLCD.
module MessagePassingAlgorithm.CBCAST.Step.Verification where

import Language.Haskell.Liquid.ProofCombinators

import Redefined
import VectorClock
import MessagePassingAlgorithm
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




-- * Step from satisfying

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




-- * Reachable from satisfying

-- | Fold right over the inputs, applying them to the process. Since stepShim
-- is inlined to LH, we have to fully apply it here by inlining foldr.
{-@
foldrInputs :: p:P r -> [IasP r {p}] -> PasP r {p} @-}
foldrInputs :: P r -> [Input r] -> P r
foldrInputs p [] = p
foldrInputs p (x:xs) = stepShim x (foldrInputs p xs)
{-@ reflect foldrInputs @-}

flip :: (a -> b -> c) -> b -> a -> c
flip f b a = f a b
{-@ inline flip @-}

{-@
reachableFromCHApres :: n:Nat -> i:[Isized r {n}] -> CHApreservation r {n} {flip foldrInputs i} @-}
reachableFromCHApres :: Int -> [Input r] -> P r -> Proof -> Proof
reachableFromCHApres _n [] p pCHA =
    pCHA
    ? (foldrInputs p [] {- === p -})
reachableFromCHApres n (x:xs) p pCHA =
    let prev = foldrInputs p xs
        prevCHA = reachableFromCHApres n xs p pCHA in
    stepCHApres x prev prevCHA
    ? (foldrInputs p (x:xs) {- === stepShim x (foldrInputs p xs) -})

{-@
reachableFromPLCDpres :: n:Nat -> i:[Isized r {n}] -> PLCDpreservation' r {n} {flip foldrInputs i} @-}
reachableFromPLCDpres :: Int -> [Input r] -> P r -> Proof -> (M r -> M r -> Proof) -> M r -> M r -> Proof




-- * Reachable from empty

data Reachable r = Reachable
    { reachableN :: Int
    , reachablePID :: PID
    , reachableInputs :: [Input r]
    , reachableProcess :: P r
    }
{-@
data Reachable [reachableSize] r = Reachable
    { reachableN :: Nat
    , reachablePID :: PIDsized {reachableN}
    , reachableInputs :: [Isized r {reachableN}]
    , reachableProcess :: {p : Psized r {reachableN} | p == foldrInputs (pEmpty reachableN reachablePID) reachableInputs }
    }
@-}
reachableSize :: Reachable r -> Int
reachableSize (Reachable _ _ inputs _) = listLength inputs
{-@ measure reachableSize @-}

{-@
reachableCHA :: p:Reachable r -> ClockHistoryAgreement {reachableProcess p} @-}
reachableCHA :: Reachable r -> Proof
reachableCHA (Reachable n p_id xs p) =
    reachableFromCHApres n xs (pEmpty n p_id) (pEmptyCHA n p_id)

{-@
reachablePLCD :: p:Reachable r -> PLCD r {reachableProcess p} @-}
reachablePLCD :: Eq r => Reachable r -> M r -> M r -> Proof
reachablePLCD (Reachable n p_id [] p) =
    pEmptyPLCD n p_id
    ? (p === foldrInputs (pEmpty n p_id) [] {- === pEmpty n p_id -})
reachablePLCD (Reachable n p_id (x:xs) p) =
    let previous = Reachable n p_id xs (foldrInputs (pEmpty n p_id) xs) in
    stepPLCDpres x (reachableProcess previous) (reachableCHA previous) (reachablePLCD previous)
    ? (p === foldrInputs (pEmpty n p_id) (x:xs) {- === stepShim x (foldrInputs (pEmpty n p_id) xs) -})
