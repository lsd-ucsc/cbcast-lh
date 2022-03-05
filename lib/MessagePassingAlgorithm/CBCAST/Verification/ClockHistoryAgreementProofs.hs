
module MessagePassingAlgorithm.CBCAST.Verification.ClockHistoryAgreementProofs where

import Language.Haskell.Liquid.ProofCombinators

import Redefined
import VectorClock
import MessagePassingAlgorithm
import MessagePassingAlgorithm.CBCAST
import MessagePassingAlgorithm.VectorClockAdapter

import VectorClock.Verification
import MessagePassingAlgorithm.CBCAST.Verification.Shims
import MessagePassingAlgorithm.CBCAST.Verification.ClockHistoryAgreement



-- * receive

{-@ ple receiveCHApres @-}
{-@
receiveCHApres :: m:M r -> CHApreservation r {len (mVC m)} {internalReceive m} @-}
receiveCHApres :: M r -> P r -> Proof -> Proof
receiveCHApres m p _pCHA
    | mSender m == pID p = () -- pHist is unchanged
    | otherwise = () -- pHist is unchanged




-- * deliver

{-@
deliverCHApres :: n:Nat -> CHApreservation r {n} {deliverShim} @-}
deliverCHApres :: Int -> P r -> Proof -> Proof
deliverCHApres n p _pCHA =
  case dequeue (pVC p) (pDQ p) of -- by cases of internalDeliver
  Nothing ->
    {-by def of deliverShim -}  case internalDeliver p of Nothing -> p
    {-p is unchanged-}          *** QED
  Just (m, pDQ') ->
    let
    p' = deliverShim p
    e = Deliver (pID p) (coerce m)
    deliverBody
        =   internalDeliver p
        === Just (m, p
            { pVC = pVC p `vcCombine` mVC m
            , pDQ = pDQ'
            , pHist = Deliver (pID p) (coerce m) : pHist p
            })
    pVCLemma
        =   pVC p'
            ? deliverBody
        === pVC p `vcCombine` mVC m
    pHistVCLemma
        =   pHistVC p'
            ? deliverBody
            ? pHistVC_unfoldDeliver n p m e p'
        === mVC m `vcCombine` pHistVC p
            ? vcCombineCommutativity n (mVC m) (pHistVC p)
        === pHistVC p `vcCombine` mVC m
    in
        vcLessEqual (pHistVC p') (pVC p')
        ? pVCLemma
        ? pHistVCLemma
    === vcLessEqual (pHistVC p `vcCombine` mVC m) (pVC p `vcCombine` mVC m)
        ? vcCombineVCLessEqualMonotonicLeft n (pHistVC p) (pVC p) (mVC m)
    === vcLessEqual (pHistVC p) (pVC p)
    *** QED




-- * broadcast

{-@
broadcastPrepareInjectCHApres :: raw:r -> n:Nat -> CHApreservation r {n} {broadcastPrepareInjectShim raw} @-}
broadcastPrepareInjectCHApres :: r -> Int -> P r -> Proof -> Proof
broadcastPrepareInjectCHApres raw n p _pCHA =
    let
    m = broadcastHelper_prepareMessage raw p
    e = Broadcast (coerce m)
    p' = broadcastHelper_injectMessage m p
    injectMessageBody
        =   broadcastHelper_injectMessage m p
        === p { pDQ = m : pDQ p
              , pHist = Broadcast (coerce m) : pHist p }
    pVCLemma
        =   pVC p'
            ? injectMessageBody
        === pVC p
    pHistLemma
        =   pHist p'
            ? injectMessageBody
        === e : pHist p
    in
        vcLessEqual (pHistVC p') (pVC p')
        ? pVCLemma
    === vcLessEqual (pHistVC p') (pVC p)
        ? pHistLemma
        ? pHistVC_unfoldBroadcast n p m e p'
    === vcLessEqual (pHistVC p) (pVC p)
    *** QED

{-@
broadcastCHApres :: raw:r -> n:Nat -> CHApreservation r {n} {broadcastShim raw} @-}
broadcastCHApres :: r -> Int -> P r -> Proof -> Proof
broadcastCHApres raw n p pCHA =
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

    -- convert evidence from p to p'
    p'CHA = broadcastPrepareInjectCHApres raw n p pCHA
    -- convert evidence from p' to p''
    p''CHA = deliverCHApres n p' p'CHA
    in
    p''CHA ? broadcastBody
