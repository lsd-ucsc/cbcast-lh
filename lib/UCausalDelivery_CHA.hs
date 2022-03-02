{-# OPTIONS_GHC "-Wno-unused-imports" #-}

-- | Clock-history agreement definition.
module UCausalDelivery_CHA where

import Language.Haskell.Liquid.ProofCombinators
import Redefined.Fin
import Redefined.Ord -- For LH reflected & aliases
--import Redefined.Proof (proofConst)

import SystemModel
import Properties
import Properties2
import UCausalDelivery

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

{-@ ple pEmptyCHA @-}
{-@
pEmptyCHA :: n:Nat -> p_id:PIDsized {n} -> ClockHistoryAgreement {pEmpty n p_id} @-}
pEmptyCHA :: Int -> Fin -> Proof
pEmptyCHA n p_id =
    let p = pEmpty n p_id in
        pHistVC p `vcLessEqual` pVC p -- restate conclusion
    === vcEmpty n `vcLessEqual` vcEmpty n -- by def of pEmpty,pHistVC,pHistVCHelper
        ? vcLessEqualReflexive (vcEmpty n)
    *** QED




-- * Hist VC

{-@
eventMessage :: n:Nat -> Event (VCMMsized {n}) r -> Msized r {n} @-}
eventMessage :: Int -> Event VCMM r -> M r
eventMessage _n (Broadcast (Message a b)) = Message a b
eventMessage _n (Deliver _pid (Message a b)) = Message a b
{-@ reflect eventMessage @-}

{-@
pHistVCHelper :: n:Nat -> Hsized r {n} -> VCsized {n} @-}
pHistVCHelper :: Int -> H r -> VC
pHistVCHelper n [] = vcEmpty n
pHistVCHelper n (Broadcast{}:es) = pHistVCHelper n es
pHistVCHelper n (e@Deliver{}:es) = mVC (eventMessage n e) `vcCombine` pHistVCHelper n es
{-@ reflect pHistVCHelper @-}

-- | The supremum of vector clocks on delivered messages in a process history.
{-@
pHistVC :: p:P r -> VCasP {p} @-}
pHistVC :: P r -> VC
pHistVC p = pHistVCHelper (listLength (pVC p)) (pHist p)
{-@ reflect pHistVC @-}




-- * Generic lemmas

{-@ tailElem :: e:_ -> {x:_ | e /= x} -> {yzs:_ | listElem e (cons x yzs)} -> { listElem e yzs } @-}
tailElem :: Eq a => a -> a -> [a] -> Proof
tailElem e x []             =   impossible
    {-restate premise-}     $   listElem e (x:[])
    {-by def of listElem-}  === (e==x || listElem e [])
    {-by e/=x premise-}     === listElem e []
    {-premise failed-}      *** QED
tailElem e x (y:zs)
    {-restate premise-}     =   listElem e (x:y:zs)
    {-by def of listElem-}  === (e==x || listElem e (y:zs))
    {-by e/=x premise-}     === listElem e (y:zs)
                            *** QED




-- * Hist VC lemmas

isBroadcast :: Event m r -> Bool
isBroadcast Broadcast{} = True
isBroadcast _ = False
{-@ measure isBroadcast @-}

isDeliver :: Event m r -> Bool
isDeliver Deliver{} = True
isDeliver _ = False
{-@ measure isDeliver @-}

--- Consider using isDeliver instead of "== Deliver ..."
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
    === pHistVCHelper (listLength (pVC p₁)) (pHist p₁)
    === pHistVCHelper n (e : pHist p₀)
    === mVC (eventMessage n e) `vcCombine` pHistVCHelper n (pHist p₀)
        ? eventMessageBody
    === mVC m `vcCombine` pHistVCHelper n (pHist p₀)
    === mVC m `vcCombine` pHistVCHelper (listLength (pVC p₀)) (pHist p₀)
    === mVC m `vcCombine` pHistVC p₀
    *** QED

--- Consider using isBroadcast instead of "== Broadcast ..."
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
    === pHistVCHelper (listLength (pVC p₁)) (pHist p₁)
    === pHistVCHelper n (e : pHist p₀)
        --- by def of pHistVCHelper which skips over Broadcasts
    === pHistVCHelper n (pHist p₀)
    === pHistVCHelper (listLength (pVC p₀)) (pHist p₀)
    === pHistVC p₀
    *** QED
-- QQQ: Does this definition pass when you add a check-var annotation for it?

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
    === mVC (eventMessage n e) `vcLessEqual` pHistVCHelper (listLength (pVC p)) (pHist p) -- by def of pHistVC
    === mVC (eventMessage n e) `vcLessEqual` pHistVCHelper n (pHist p) -- by premise about VC sizes
        ? histElemLessEqualHistVC_lemma n e (pHist p)
    *** QED

{-@
histElemLessEqualHistVC_lemma
    ::     n:Nat
    -> {   e:Event (VCMMsized {n}) r | isDeliver e }
    -> { hhs:Hsized r {n} | listElem e hhs }
    -> { vcLessEqual (mVC (eventMessage n e)) (pHistVCHelper n hhs) }
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
    hsVC = pHistVCHelper n hs
    hhsVC = pHistVCHelper n (h:hs)
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
    hsVC = pHistVCHelper n hs
    hhsVC = pHistVCHelper n (h:hs)
        === hVC `vcCombine` hsVC -- h is Deliver
