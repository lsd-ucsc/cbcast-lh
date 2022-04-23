{-# OPTIONS_GHC "-Wno-unused-imports" #-} -- LH needs bodies of reflected definitions
{-# OPTIONS_GHC "-Wno-warnings-deprecations" #-} -- Hide the "verification only" and "internal use" warnings

module CBCAST.Verification.PLCDpresBroadcast {-# WARNING "Verification only" #-} where

import Language.Haskell.Liquid.ProofCombinators (Proof, (===), (***), QED(..), (?))
import Language.Haskell.Liquid.ProofCombinatorsExtra (proofConst)

import Redefined
import VectorClock
import CBCAST.Core
import CBCAST.Transitions
import Redefined.Verification
import CBCAST.Verification.ProcessOrder
import CBCAST.Verification.PLCDpres
import CBCAST.Verification.PLCDpresDeliver


-- * PLCD preservation of Broadcast

-- | The first two steps of broadcast (prepare and inject message) without the
-- third step (deliver).
{-@ broadcastPrepareInjectShim :: r -> p:Process r -> PasP r {p} @-}
broadcastPrepareInjectShim :: r -> Process r -> Process r
broadcastPrepareInjectShim raw p =
    broadcastHelper_inject (broadcastHelper_prepare raw p) p
{-@ inline broadcastPrepareInjectShim @-}

-- | The broadcast helpers, to /prepare/ and /inject/ the message into the
-- process, preserve PLCD.
{-@
broadcastPrepareInjectPLCDpres :: raw:r -> n:Nat -> PLCDpreservation r {n} {broadcastPrepareInjectShim raw} @-}
broadcastPrepareInjectPLCDpres :: Eq r => r -> Int -> Process r -> (Message r -> Message r -> Proof)
                                                                -> (Message r -> Message r -> Proof)
broadcastPrepareInjectPLCDpres raw _n p pPLCD m₁ m₂ =
    let
    m = broadcastHelper_prepare raw p
    p' = broadcastHelper_inject m p
    e₁ = Deliver (pID p') m₁
    e₂ = Deliver (pID p') m₂
    e₃ = Broadcast m
    injectMessageBody
        =   broadcastHelper_inject m p
        === p { pDQ = m : pDQ p
              , pHist = Broadcast m : pHist p
                  `proofConst` internalBroadcastCHA m (pVC p) (pHist p)
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

-- | The internalBroadcast function, but throw away the message.
{-@ broadcastShim :: r -> p:Process r -> PasP r {p} @-}
broadcastShim :: r -> Process r -> Process r
broadcastShim raw p =
    let (_, p') = internalBroadcast raw p in p'
{-@ inline broadcastShim @-}

-- | The broadcast transition preserves PLCD.
{-@
broadcastPLCDpres :: raw:r -> n:Nat -> PLCDpreservation r {n} {broadcastShim raw} @-}
broadcastPLCDpres :: Eq r => r -> Int -> Process r -> (Message r -> Message r -> Proof)
                                                   -> (Message r -> Message r -> Proof)
broadcastPLCDpres raw n p pPLCD = -- ∀ m m'
    let
    p' = broadcastPrepareInjectShim raw p
    p'' = broadcastShim raw p
    -- relate p and p' and p''
    broadcastBody                       =   p''
    --  {-by def of p''-}               === broadcastShim raw p
        {-by def of broadcastShim-}     === (let (_m, _p) = internalBroadcast raw p in _p)
        ? broadcastAlwaysDelivers raw p
    --  {-by def of internalBroadcast-} === (let _m = broadcastHelper_prepare raw p
    --                                           _p = broadcastHelper_inject _m p
    --                                           Just (__m, __p) = internalDeliver _p in __p)
    --  {-by composition of functions-} === (let _p = broadcastHelper_inject (broadcastHelper_prepare raw p) p
    --                                           Just (__m, __p) = internalDeliver _p in __p)
    --  {-by def of prepareInjectShim-} === (let _p = broadcastPrepareInjectShim raw p
    --                                           Just (__m, __p) = internalDeliver _p in __p)
        {-by def of p'-}                === (let Just (__m, __p) = internalDeliver p' in __p)
    -- convert evidence from p to p'
    p'PLCD = broadcastPrepareInjectPLCDpres raw n p pPLCD -- ∀ m m'
    -- convert evidence from p' to p''
    p''PLCD = deliverPLCDpres n p' p'PLCD -- ∀ m m'
    in
    (p''PLCD ? broadcastBody) -- ∀ m m'
