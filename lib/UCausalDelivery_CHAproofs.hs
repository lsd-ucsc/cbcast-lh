
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

{-@
deliverCHApres :: n:Nat -> CHApreservation r {n} {deliverShim} @-}
deliverCHApres :: Int -> P r -> Proof -> Proof
deliverCHApres n p _pCHA =
  case dequeue (pVC p) (pDQ p) of -- by cases of deliver
  Nothing ->
    {-by def of deliverShim -}  case deliver p of Nothing -> p
    {-p is unchanged-}          *** QED
  Just (m, pDQ') ->
    let
    p' = deliverShim p
    n = listLength (pVC p)
    e = Deliver (pID p) (coerce m)
    deliverBody
        =   deliver p
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
