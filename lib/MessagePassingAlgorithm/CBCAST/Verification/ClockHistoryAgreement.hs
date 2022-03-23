{-# OPTIONS_GHC "-Wno-unused-imports" #-} -- LH needs bodies of reflected definitions

-- | Clock-history agreement definition for a CBCAST process, and a few lemmas
-- about it.
module MessagePassingAlgorithm.CBCAST.Verification.ClockHistoryAgreement where

import Language.Haskell.Liquid.ProofCombinators

import Redefined
import VectorClock
import MessagePassingAlgorithm
import MessagePassingAlgorithm.VectorClockAdapter
import MessagePassingAlgorithm.CBCAST

import Redefined.Verification
import VectorClock.Verification

{-@
type ClockHistoryAgreement P
    = {_ : Proof | vcLessEqual (pHistVC P) (pVC P) }
@-}

{-@
type CHApreservation r N OP
    =  p:Psized r {N}
    -> ClockHistoryAgreement {p}
    -> ClockHistoryAgreement {OP p}
@-}

-- | The empty CBCAST process observes clock history agreement. This proof is
-- in this module because it exercises the definition of CHA and forces LH to
-- resolve all the symbols.
{-@ ple pEmptyCHA @-}
{-@
pEmptyCHA :: n:Nat -> p_id:PIDsized {n} -> ClockHistoryAgreement {pEmpty n p_id} @-}
pEmptyCHA :: Int -> Fin -> Proof
pEmptyCHA n p_id =
    let p = pEmpty n p_id in
        pHistVC p `vcLessEqual` pVC p -- restate conclusion
    === vcEmpty n `vcLessEqual` vcEmpty n -- by def of pEmpty,pHistVC,histVC
        ? vcLessEqualReflexive (vcEmpty n)
    *** QED




-- * Hist VC lemmas

-- CHA_MIGRATION: This doesn't need it's own name anymore. Also, the
-- implementation is in MPA.VCA now.
{-@
pHistVC :: p:P r -> VCasP {p} @-}
pHistVC :: P r -> VC
pHistVC p = histVC (listLength (pVC p)) (pHist p)
{-@ reflect pHistVC @-}


isBroadcast :: Event m r -> Bool
isBroadcast Broadcast{} = True
isBroadcast _ = False
{-@ measure isBroadcast @-}

isDeliver :: Event m r -> Bool
isDeliver Deliver{} = True
isDeliver _ = False
{-@ measure isDeliver @-}

-- | After adding a deliver event the new histVC is the old one combined with
-- the delivered message vc.
--
-- XXX Consider using isDeliver instead of "== Deliver ..."
{-@
pHistVC_unfoldDeliver
    ::   n:Nat
    ->  p0:Psized r {n}
    ->   m:Msized r {n}
    -> { e:Event (VCMMsized {n}) r | e == Deliver (pID p0) m }
    -> {p1:Psized r {n} | pHist p1 == cons e (pHist p0) }
    -> { pHistVC p1 == vcCombine (mVC m) (pHistVC p0) }
@-}
pHistVC_unfoldDeliver :: Int -> P r -> M r -> Event VCMM r -> P r -> Proof
pHistVC_unfoldDeliver _n p₀ m e@Broadcast{} _p₁
    = impossible
    $ e === Deliver (pID p₀) m -- restate (failed) premise
pHistVC_unfoldDeliver n p₀ m@(Message x y) e@Deliver{} p₁ =
    let
    eventMessageBody
        =   eventMessage n e
        === eventMessage n (Deliver (pID p₀) (Message x y))
        === Message x y
        === m
    in
        pHistVC p₁
    === histVC (listLength (pVC p₁)) (pHist p₁)
    === histVC n (e : pHist p₀)
    === mVC (eventMessage n e) `vcCombine` histVC n (pHist p₀)
        ? eventMessageBody
    === mVC m `vcCombine` histVC n (pHist p₀)
    === mVC m `vcCombine` histVC (listLength (pVC p₀)) (pHist p₀)
    === mVC m `vcCombine` pHistVC p₀
    *** QED

-- | After adding a broadcast event the new histVC is the same as the old one.
--
-- XXX Consider using isBroadcast instead of "== Broadcast ..."
{-@
pHistVC_unfoldBroadcast
    ::   n:Nat
    ->  p0:Psized r {n}
    ->   m:Msized r {n}
    -> { e:Event (VCMMsized {n}) r | e == Broadcast m }
    -> {p1:Psized r {n} | pHist p1 == cons e (pHist p0) }
    -> { pHistVC p1 == pHistVC p0 }
@-}
pHistVC_unfoldBroadcast :: Int -> P r -> M r -> Event VCMM r -> P r -> Proof
pHistVC_unfoldBroadcast _n _p₀ m e@Deliver{} _p₁
    = impossible
    $ e === Broadcast m -- restate (failed) premise
pHistVC_unfoldBroadcast n p₀ _m e@Broadcast{} p₁ =
        pHistVC p₁
    === histVC (listLength (pVC p₁)) (pHist p₁)
    === histVC n (e : pHist p₀)
        --- by def of histVC which skips over Broadcasts
    === histVC n (pHist p₀)
    === histVC (listLength (pVC p₀)) (pHist p₀)
    === pHistVC p₀
    *** QED
-- QQQ: Does this definition pass when you add a check-var annotation for it?

-- | The VCs of messages on deliveries in the history are all less-equal than
-- the histVC of the whole history.
{-@
histElemLessEqualHistVC
    ::   n:Nat
    -> { e:Event (VCMMsized {n}) r | isDeliver e }
    -> { p:Psized r {n} | listElem e (pHist p) }
    -> { vcLessEqual (mVC (eventMessage n e)) (pHistVC p) }
@-}
histElemLessEqualHistVC :: Eq r => Int -> Event VCMM r -> P r -> Proof
histElemLessEqualHistVC n e p =
        mVC (eventMessage n e) `vcLessEqual` pHistVC p -- restate conclusion
    === mVC (eventMessage n e) `vcLessEqual` histVC (listLength (pVC p)) (pHist p) -- by def of pHistVC
    === mVC (eventMessage n e) `vcLessEqual` histVC n (pHist p) -- by premise about VC sizes
        ? histElemLessEqualHistVC_lemma n e (pHist p)
    *** QED

{-@
histElemLessEqualHistVC_lemma
    ::     n:Nat
    -> {   e:Event (VCMMsized {n}) r | isDeliver e }
    -> { hhs:Hsized r {n} | listElem e hhs }
    -> { vcLessEqual (mVC (eventMessage n e)) (histVC n hhs) }
@-}
histElemLessEqualHistVC_lemma :: Eq r => Int -> Event VCMM r -> H r -> Proof
histElemLessEqualHistVC_lemma _n e@Deliver{} [] =
    impossible $ listElem e [] -- restate (failed) premise
histElemLessEqualHistVC_lemma n e@Deliver{} (h@Broadcast{}:hs) =
                                            True
    ? tailElem e h hs
    ? histElemLessEqualHistVC_lemma n e hs  === eVC `vcLessEqual` hsVC
                                            === eVC `vcLessEqual` hhsVC
                                            *** QED
  where
    eVC = mVC (eventMessage n e)
    hsVC = histVC n hs
    hhsVC = histVC n (h:hs)
        === hsVC -- h is Broadcast

histElemLessEqualHistVC_lemma n e@Deliver{} (h@Deliver{}:hs)
  | e == h =
                                        True
    ? vcCombineResultLarger hVC hsVC    === hVC `vcLessEqual` hhsVC
                                        *** QED
  | otherwise =
                                                True
    ? tailElem e h hs
    ? histElemLessEqualHistVC_lemma n e hs      === eVC `vcLessEqual` hsVC
    ? vcCombineResultLarger hVC hsVC            === hsVC `vcLessEqual` hhsVC
    ? vcLessEqualTransitive n eVC hsVC hhsVC    === eVC `vcLessEqual` hhsVC
                                                *** QED
  where
    eVC = mVC (eventMessage n e)
    hVC = mVC (eventMessage n h)
    hsVC = histVC n hs
    hhsVC = histVC n (h:hs)
        === hVC `vcCombine` hsVC -- h is Deliver
