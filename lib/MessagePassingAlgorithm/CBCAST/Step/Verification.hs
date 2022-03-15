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
        prevCHA = reachableFromCHApres n xs p pCHA
    in
    stepCHApres x prev prevCHA
    ? (foldrInputs p (x:xs) {- === stepShim x (foldrInputs p xs) -})

{-@
reachableFromPLCDpres :: n:Nat -> i:[Isized r {n}] -> PLCDpreservation' r {n} {flip foldrInputs i} / [len i] @-}
reachableFromPLCDpres :: Eq r => Int -> [Input r] -> P r -> Proof -> (M r -> M r -> Proof) -> M r -> M r -> Proof
reachableFromPLCDpres _n [] p _pCHA pPLCD = -- ∀ m m'
    pPLCD -- ∀ m m'
    ? (foldrInputs p [] {- === p -})
reachableFromPLCDpres n (x:xs) p pCHA pPLCD =
    let prev = foldrInputs p xs
        prevCHA = reachableFromCHApres n xs p pCHA
        prevPLCD = reachableFromPLCDpres n xs p pCHA pPLCD
    in
    stepPLCDpres x prev prevCHA prevPLCD -- ∀ m m'
    ? (foldrInputs p (x:xs) {- === stepShim x (foldrInputs p xs) -})




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
reachableCHA (Reachable n p_id xs _p) =
    reachableFromCHApres n xs (pEmpty n p_id) (pEmptyCHA n p_id)

{-@
reachablePLCD :: p:Reachable r -> PLCD r {reachableProcess p} @-}
reachablePLCD :: Eq r => Reachable r -> M r -> M r -> Proof
reachablePLCD (Reachable n p_id xs _p) =
    reachableFromPLCDpres n xs (pEmpty n p_id) (pEmptyCHA n p_id) (pEmptyPLCD n p_id)



type C = Integer
{-@ type C = {c:Integer | 0 <= c} @-}

type Vc = [C]
{-@ type Vc = [C] @-} -- This alias ensures vc contents are Integer|0<=n
{-@ type VcN N = {v:Vc | len v == N} @-}
{-@ type VcV V = VcN {len V} @-}

type Pid = Int
{-@ type PidN N = {p:Nat | p < N} @-}
{-@ type PidV V = PidN {len V} @-}

data Ev
    = Bcast {bcastVC :: Vc}
    | Deliv {delivVC :: Vc}
{-@
data Ev
    = Bcast {bcastVC :: Vc}
    | Deliv {delivVC :: Vc}
@-}

{-@ evVc :: Ev -> Vc @-}
evVc :: Ev -> Vc
evVc (Bcast v) = v
evVc (Deliv v) = v
{-@ measure evVc @-}

{-@ type EvN N = {e:Ev | len (evVc e) == N } @-}
{-@ type EvV V = EvN {len V} @-}
{-@ type EvE E = EvV {evVc E} @-}

{-@
replicate' :: n:Nat -> a -> {xs:[a] | len xs == n} @-}
replicate' :: Int -> a -> [a]
replicate' 0 _x = []
replicate' n x = x : replicate' (n - 1) x
{-@ reflect replicate' @-}

max' :: Ord a => a -> a -> a
max' x y
    | x < y = y
    | otherwise = x
{-@ reflect max' @-}

{-@
combine :: v:Vc -> VcV {v} -> VcV {v} @-}
combine :: Vc -> Vc -> Vc
combine [] [] = []
combine (x:xs) (y:ys) = (max' x y) : combine xs ys
{-@ reflect combine @-}

{-@
histVC :: n:Nat -> [EvN {n}] -> VcN {n} @-}
histVC :: Int -> [Ev] -> Vc
histVC n [] = replicate' n 0
histVC n (Bcast _:es) = histVC n es
histVC n (Deliv v:es) = combine v (histVC n es)
{-@ reflect histVC @-}

data HistoryClock = HistoryClock
    { vc :: Vc
    , pid :: Pid
    , hist :: [Ev]
    }
{-@
data HistoryClock = HistoryClock
    { vc :: Vc
    , pid :: PidV {vc}
    , hist :: {h:[EvV {vc}] | histVC (len vc) h == vc}
    }
@-}

{-@ type HcN N = {h:HistoryClock | len (vc h) == N} @-}
{-@ type HcV V = HcN {len V} @-}
{-@ type HcH H = HcV {vc H} @-}

{-@ type VcH H = VcV {vc H} @-}

{-@
tick :: v:Vc -> PidV {v} -> VcV {v} @-}
tick :: Vc -> Pid -> Vc
tick (x:xs) 0 = (x + 1):xs
tick (x:xs) n = x:tick xs (n - 1)
{-@ reflect tick @-}

-- | Record a broadcast event in the history and return its clock.
{-@
bcast :: h:HistoryClock -> (VcH {h}, HcH {h}) @-}
bcast :: HistoryClock -> (Vc, HistoryClock)
bcast h =
    let vc' = tick (vc h) (pid h) in
    ( vc'
    , h{hist = Bcast vc':hist h}
    )
{-@ ple bcast @-} -- histVC n (Bcast v:h) === histVC n h
{-@ reflect bcast @-}

{-@
deliv :: v:Vc -> HcV {v} -> HcV {v} @-}
deliv :: Vc -> HistoryClock -> HistoryClock
deliv v h = h
    { vc = combine v (vc h)
    , hist = Deliv v:hist h
    }
{-@ ple deliv @-} -- histVC n (Deliv v:h) === combine v (histVC n h)
{-@ reflect deliv @-}
