{-# OPTIONS_GHC "-Wno-unused-imports" #-} -- LH needs bodies of reflected definitions
{-# OPTIONS_GHC "-Wno-warnings-deprecations" #-} -- Hide the "verification only" and "internal use" warnings

module CBCAST.Verification.PIDpresStep {-# WARNING "Verification only" #-} where

import Language.Haskell.Liquid.ProofCombinators (Proof, (===), (***), QED(..), (?))
import Language.Haskell.Liquid.ProofCombinatorsExtra (proofConst)

import Redefined
import VectorClock
import CBCAST.Core
import CBCAST.Step
import CBCAST.Transitions
import CBCAST.Verification.PLCDpresBroadcast (broadcastShim, broadcastPrepareInjectShim)
import CBCAST.Verification.PLCDpresDeliver (deliverShim)
import CBCAST.Verification.PLCDpresStep (stepShim)

{-@
stepPIDpres
    :: n:Nat -> op:OPsized r {n} -> p:Psized r {n}
    -> { pID p == pID (stepShim op p) }
@-}
stepPIDpres :: Int -> Op r -> Process r -> Proof
stepPIDpres _n op p =
  case op of
    OpReceive   n m -> receivePIDpres   n m p ? (step op p === ResultReceive   n (internalReceive   m p))
    OpDeliver   n   -> deliverPIDpres   n   p ? (step op p === ResultDeliver   n (internalDeliver     p))
    OpBroadcast n r -> broadcastPIDpres n r p ? (step op p === ResultBroadcast n (internalBroadcast r p))

{-@
receivePIDpres
    :: n:Nat -> m:Msized r {n} -> p:Psized r {n}
    -> { pID p == pID (internalReceive m p) }
@-}
receivePIDpres :: Int -> Message r -> Process r -> Proof
receivePIDpres n m p
    -- by cases of internalReceive
    | mSender m == pID p =
            internalReceive m p
        === p
        *** QED
    | otherwise =
            internalReceive m p
        === p{ pDQ = enqueue m (pDQ p) }
        *** QED

{-@ ple deliverPIDpres @-}
{-@
deliverPIDpres
    :: n:Nat -> p:Psized r {n}
    -> { pID p == pID (deliverShim p) }
@-}
deliverPIDpres :: Int -> Process r -> Proof
deliverPIDpres n p =
    -- by cases of internalDeliver
    case dequeue (pVC p) (pDQ p) of
        Nothing ->
                deliverShim p
            === p
            *** QED
        Just (m, pDQ') ->
                deliverShim p
            === p{ pVC = vcCombine (mVC m) (pVC p)
                 , pDQ = pDQ'
                 , pHist = Deliver (pID p) m : pHist p
                     `proofConst` internalDeliverCHA m (pID p) (pVC p) (pHist p)
                 }
            *** QED

{-@ ple broadcastPrepareInjectPIDpres @-}
{-@
broadcastPrepareInjectPIDpres
    :: n:Nat -> r:r -> p:Psized r {n}
    -> { pID p == pID (broadcastPrepareInjectShim r p) }
@-}
broadcastPrepareInjectPIDpres :: Int -> r -> Process r -> Proof
broadcastPrepareInjectPIDpres n raw p =
    let m = broadcastHelper_prepare raw p in
        broadcastPrepareInjectShim raw p
    === p{ pDQ = m : pDQ p
         , pHist = Broadcast m : pHist p
             `proofConst` internalBroadcastCHA m (pVC p) (pHist p)
         }
    *** QED

{-@
broadcastPIDpres
    :: n:Nat -> r:r -> p:Psized r {n}
    -> { pID p == pID (broadcastShim r p) }
@-}
broadcastPIDpres :: Int -> r -> Process r -> Proof
broadcastPIDpres n r p =
    let
    p' = broadcastPrepareInjectShim r p
    p'' = broadcastShim r p
    -- relate p and p' and p''
    broadcastBody =
            p''
        === (let (_m, _p) = internalBroadcast r p in _p)
            ? broadcastAlwaysDelivers r p
        === (let Just (__m, __p) = internalDeliver p' in __p)
    in
                                                pID p
    ? broadcastPrepareInjectPIDpres n r p   === pID p'
    ? deliverPIDpres n p'                   === pID p''
    ? broadcastBody                         *** QED
