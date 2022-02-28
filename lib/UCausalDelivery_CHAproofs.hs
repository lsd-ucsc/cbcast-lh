
module UCausalDelivery_CHAproofs where

import Language.Haskell.Liquid.ProofCombinators
import Redefined.Fin
import Redefined.Ord
import Redefined.Proof (proofConst)

import SystemModel
import Properties
import Properties2
import UCausalDelivery
import UCausalDelivery_Shims
import UCausalDelivery_CHA




-- * receive

{-@ ple receiveCHApres @-}
{-@
receiveCHApres :: m:M r -> CHApreservation r {len (mVC m)} {receive m} @-}
receiveCHApres :: M r -> P r -> Proof -> Proof
receiveCHApres m p _pCHA
    | mSender m == pID p = () -- pHist is unchanged
    | otherwise = () -- pHist is unchanged




-- * deliver

-- | DRY up with the proofs below that produce this same fact by other means
{-@ ple deliverVcIsPrevCombineMsg @-}
{-@
deliverVcIsPrevCombineMsg
    :: {p1:P r | isJust (deliver p1)}
    -> { m:M r | fst (fromJust (deliver p1)) == m }
    -> {p2:P r | snd (fromJust (deliver p1)) == p2}
    -> {vcCombine (pVC p1) (mVC m) == pVC p2}
@-}
deliverVcIsPrevCombineMsg :: P r -> M r -> P r -> Proof
deliverVcIsPrevCombineMsg p₁ m p₂ = --- by cases of deliver
    case dequeue (pVC p₁) (pDQ p₁) of -- by cases of deliver
        Just (_m, _pDQ') -> -- one case, due to premise
                pVC p₂ -- restate (part of) conclusion
            === vcCombine (pVC p₁) (mVC m) -- by def of deliver
            *** QED

-- | DRY up with the proofs below that produce this same fact by other means
{-@ ple deliverHistVcIsPrevCombineMsg @-}
{-@
deliverHistVcIsPrevCombineMsg
    :: {p1:P r | isJust (deliver p1)}
    -> { m:M r | fst (fromJust (deliver p1)) == m }
    -> {p2:P r | snd (fromJust (deliver p1)) == p2}
    -> {vcCombine (pHistVC p1) (mVC m) == pHistVC p2}
@-}
deliverHistVcIsPrevCombineMsg :: P r -> M r -> P r -> Proof
deliverHistVcIsPrevCombineMsg p₁ m p₂ =
    case dequeue (pVC p₁) (pDQ p₁) of -- by cases of deliver
        Just (_m, _pDQ') -> -- one case, due to premise
            let n = listLength (pVC p₁)
                e = Deliver (pID p₁) (coerce m)
            in  pHistVC p₂ -- restate (part of) conclusion
                ? ( pVC p₂ === vcCombine (pVC p₁) (mVC m) ) -- VCs have same length
            === pHistVCHelper n (pHist p₂) -- by def of pHistVC
                ? ( pHist p₂ === e : pHist p₁ )
            === pHistVCHelper n (e : pHist p₁) -- by def of deliver
            === vcCombine (eventVC e) (pHistVCHelper n (pHist p₁)) -- by def of pHistVCHelper
                ? (eventVC e === mVC m)
            === vcCombine (mVC m) (pHistVCHelper n (pHist p₁))
            === vcCombine (mVC m) (pHistVC p₁)
                ? vcCombineCommutativity n (mVC m) (pHistVC p₁)
            === vcCombine (pHistVC p₁) (mVC m)
            *** QED

{-@ ple deliverCHApres @-}
{-@
deliverCHApres :: n:Nat -> CHApreservation r {n} {deliverShim} @-}
deliverCHApres :: Int -> P r -> Proof -> Proof
deliverCHApres n p _pCHA = -- by cases of deliver
    case dequeue (pVC p) (pDQ p) of
        Nothing -> () -- p is unchanged
        Just (m, _pDQ) ->
            let p' = deliverShim p in
                vcLessEqual (pHistVC p') (pVC p') -- restate conclusion
                ? deliverVcIsPrevCombineMsg p m p'
                ? deliverHistVcIsPrevCombineMsg p m p'
            === vcLessEqual (pHistVC p `vcCombine` mVC m) (pVC p `vcCombine` mVC m)
            --- vcLessEqual (pHistVC p) (pVC p) -- restate premise
                ? vcCombineVCLessEqualMonotonicLeft n (pHistVC p) (pVC p) (mVC m)
            *** QED




-- * broadcast

-- TODO: also use this lemma up above to shorten deliverHistVcIsPrevCombineMsg
{-@ ple pHistVC_unfoldStep @-}
{-@
pHistVC_unfoldStep
    ::   n:Nat
    ->  p0:Psized r {n}
    ->   m:Msized r {n}
    -> { e:Event (VCMMsized {n}) r | e == Broadcast m
                                  || e == Deliver (pID p0) m }
    -> {p1:Psized r {n} | pHist p1 == cons e (pHist p0) }
    -> { pHistVC p1 == vcCombine (pHistVC p0) (mVC m) }
@-}
pHistVC_unfoldStep :: Int -> P r -> M r -> Event VCMM r -> P r -> Proof
pHistVC_unfoldStep n p₀ m e p₁ =
    let
    e_vc
        =   eventVC e
        === mVC m -- by def of eventVC, but requires PLE for some reason
    p₀histVC
                                        =   pHistVC p₀
        ? (n === listLength (pVC p₀))   === pHistVCHelper n (pHist p₀) -- by def of pHistVC, but requires PLE for some reason
    in
    {-restate (part of) conclusion-}    pHistVC p₁
    ? (n === listLength (pVC p₁))   === pHistVCHelper n (pHist p₁) -- by def of pHistVC, but requires PLE for some reason
    {-by premise-}                  === pHistVCHelper n (e : pHist p₀)
    {-by def of pHistVCHelper-}     === (eventVC e `proofConst` vcmmSizedEventVC n e) `vcCombine` pHistVCHelper n (pHist p₀)
    {-simplify-}                    === eventVC e `vcCombine` pHistVCHelper n (pHist p₀)
    ? p₀histVC                      === eventVC e `vcCombine` pHistVC p₀
    ? e_vc                          === mVC m `vcCombine` pHistVC p₀
    ? vcCombineCommutativity n (mVC m) (pHistVC p₀)
    {-restate (part of) conclusion-}=== pHistVC p₀ `vcCombine` mVC m
                                    *** QED

{-@
broadcastPrepareInjectCHApres :: raw:r -> n:Nat -> CHApreservation r {n} {broadcastPrepareInjectShim raw} @-}
broadcastPrepareInjectCHApres :: r -> Int -> P r -> Proof -> Proof
broadcastPrepareInjectCHApres raw _n p _pCHA =
    let
        p' = broadcastPrepareInjectShim raw p
    in
    ()
    *** Admit

-- FIXME: rewrite this proof in terms of deliverCHApres?
{-@
broadcastCHApres :: raw:r -> n:Nat -> CHApreservation r {n} {broadcastShim raw} @-}
broadcastCHApres :: r -> Int -> P r -> Proof -> Proof
broadcastCHApres raw n p₀ _pCHA =
    let
    -- inject new message into p₀ to obtain p₁
    m = broadcastHelper_prepareMessage raw p₀
    e = Broadcast (coerce m)
    --      ? (coerce m === m)
    --  === Broadcast m -- QQQ: Why does adding this extra information break the proof?
    p₁
                                                    =   broadcastHelper_injectMessage m p₀
        {-by def of broadcastHelper_injectMessage-} === P (pVC p₀) (pID p₀) (m : pDQ p₀) (e : pHist p₀)
    p₁vc
                                                    =   pVC p₁
        {-by def of broadcastHelper_injectMessage-} === pVC p₀
    p₁histVC
                                                =   pHistVC p₁
        ? pHistVC_unfoldStep n p₀ m e p₁        === vcCombine (pHistVC p₀) (mVC m)

    -- deliver from p₁ to obtain p₂
    Just (_m, p₂) = deliver p₁ ? broadcastAlwaysDelivers raw p₀
    p₂vc
                                                =   pVC p₂
        ? deliverVcIsPrevCombineMsg p₁ m p₂     === vcCombine (pVC p₁) (mVC m)
    p₂histVC
                                                =   pHistVC p₂
        ? deliverHistVcIsPrevCombineMsg p₁ m p₂ === vcCombine (pHistVC p₁) (mVC m)
    in
                                                vcLessEqual (pHistVC p₂) (pVC p₂) -- restate conclusion
    ? p₂histVC ? p₂vc                       === vcLessEqual (pHistVC p₁ `vcCombine` mVC m) (pVC p₁ `vcCombine` mVC m)
    ? p₁histVC ? p₁vc                       === vcLessEqual (pHistVC p₀ `vcCombine` mVC m `vcCombine` mVC m) (pVC p₀ `vcCombine` mVC m)
    ? vcCombineAssociativity n
        (pHistVC p₀) (mVC m) (mVC m)        === vcLessEqual (pHistVC p₀ `vcCombine` (mVC m `vcCombine` mVC m)) (pVC p₀ `vcCombine` mVC m)
    ? vcCombineIdempotence (mVC m)          === vcLessEqual (pHistVC p₀ `vcCombine` mVC m) (pVC p₀ `vcCombine` mVC m)
    ? vcCombineVCLessEqualMonotonicLeft n
        (pHistVC p₀) (pVC p₀) (mVC m)       === vcLessEqual (pHistVC p₀) (pVC p₀) -- restate premise
                                            *** QED
