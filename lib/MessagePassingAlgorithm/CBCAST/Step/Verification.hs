{-# OPTIONS_GHC "-Wno-unused-imports" #-} -- LH needs bodies of reflected definitions

-- Proof that step preserves PLCD.
module MessagePassingAlgorithm.CBCAST.Step.Verification where

import Prelude hiding (foldr)

import Language.Haskell.Liquid.ProofCombinators

import Redefined
import VectorClock
import MessagePassingAlgorithm
import MessagePassingAlgorithm.VectorClockAdapter
import MessagePassingAlgorithm.CBCAST
import MessagePassingAlgorithm.CBCAST.Step

import MessagePassingAlgorithm.VectorClockAdapter.Verification.ProcessLocalCausalDelivery
import MessagePassingAlgorithm.CBCAST.Verification.ClockHistoryAgreement
import MessagePassingAlgorithm.CBCAST.Verification.PLCD
import MessagePassingAlgorithm.CBCAST.Verification.PLCD.Receive
import MessagePassingAlgorithm.CBCAST.Verification.PLCD.Deliver
import MessagePassingAlgorithm.CBCAST.Verification.PLCD.Broadcast




-- * Step from satisfying

-- | The stepOrig function but drops the output.
{-@ stepOrigShim :: i:Input r -> PasI r {i} -> PasI r {i} @-}
stepOrigShim :: Input r -> P r -> P r
stepOrigShim i p₀ = case stepOrig i p₀ of
    OutputReceive _ p             -> p
    OutputBroadcast _ (_, p)      -> p
    OutputDeliver _ (Just (_, p)) -> p
    OutputDeliver _ Nothing       -> p₀
{-@ inline stepOrigShim @-}

{-@
stepOrigPLCDpres :: i:Input r -> PLCDpreservation r {inputSize i} {stepOrigShim i} @-}
stepOrigPLCDpres :: Eq r => Input r -> P r -> (M r -> M r -> Proof) -> M r -> M r -> Proof
stepOrigPLCDpres i p pPLCD = -- ∀ m m'
  case i of
    InputReceive   n m -> receivePLCDpres   m   p pPLCD ? (stepOrig i p === OutputReceive   n (internalReceive   m p))
    InputDeliver   n   -> deliverPLCDpres     n p pPLCD ? (stepOrig i p === OutputDeliver   n (internalDeliver     p))
    InputBroadcast n r -> broadcastPLCDpres r n p pPLCD ? (stepOrig i p === OutputBroadcast n (internalBroadcast r p))




-- * Reachable from satisfying

-- | Fold right over the inputs, applying them to the process. Since stepOrigShim
-- is inlined to LH, we have to fully apply it here by inlining foldr.
{-@
foldrInputs :: p:P r -> [IasP r {p}] -> PasP r {p} @-}
foldrInputs :: P r -> [Input r] -> P r
foldrInputs p [] = p
foldrInputs p (x:xs) = stepOrigShim x (foldrInputs p xs)
{-@ reflect foldrInputs @-}

flip :: (a -> b -> c) -> b -> a -> c
flip f b a = f a b
{-@ inline flip @-}

{-@
trcOrigPLCDpres
    :: n:Nat
    -> i:[Isized r {n}]
    -> PLCDpreservation r {n} {flip foldrInputs i}
@-}
trcOrigPLCDpres :: Eq r => Int -> [Input r] -> P r -> (M r -> M r -> Proof) -> M r -> M r -> Proof
trcOrigPLCDpres _n [] p pPLCD = -- ∀ m m'
    pPLCD -- ∀ m m'
    ? (foldrInputs p [] {- === p -})
trcOrigPLCDpres n (x:xs) p pPLCD =
    let prev = foldrInputs p xs
        prevPLCD = trcOrigPLCDpres n xs p pPLCD
    in
    stepOrigPLCDpres x prev prevPLCD -- ∀ m m'
    ? (foldrInputs p (x:xs) {- === stepOrigShim x (foldrInputs p xs) -})




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
reachablePLCD :: p:Reachable r -> PLCD r {reachableProcess p} @-}
reachablePLCD :: Eq r => Reachable r -> M r -> M r -> Proof
reachablePLCD (Reachable n p_id xs _p) =
    trcOrigPLCDpres n xs (pEmpty n p_id) (pEmptyPLCD n p_id)
