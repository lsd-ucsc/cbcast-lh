
-- Proof that broadcast preserves PLCD.
module UCausalDelivery_PLCDbroadcast where

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
import UCausalDelivery_PLCD
import UCausalDelivery_PLCDdeliver

{-@
broadcastPrepareInjectPLCDpres :: raw:r -> n:Nat -> PLCDpreservation' r {n} {broadcastPrepareInjectShim raw} @-}
broadcastPrepareInjectPLCDpres :: Eq r => r -> Int -> P r -> Proof -> (M r -> M r -> Proof) -> M r -> M r -> Proof
broadcastPrepareInjectPLCDpres _raw _n _p _pCHA _pPLCD _m₁ _m₂ =
    () *** Admit

{-@
broadcastPLCDpres :: raw:r -> n:Nat -> PLCDpreservation' r {n} {broadcastShim raw} @-}
broadcastPLCDpres :: Eq r => r -> Int -> P r -> Proof -> (M r -> M r -> Proof) -> M r -> M r -> Proof
broadcastPLCDpres raw n p pCHA pPLCD = -- ∀ m m'
    let
    p' = broadcastPrepareInjectShim raw p
    p'' = broadcastShim raw p

    -- relate p and p' and p''
    broadcastBody                                   =   p''
    --  {-by def of p''-}                           === broadcastShim raw p
        {-by def of broadcastShim-}                 === (let (_m, _p) = broadcast raw p in _p)
        ? broadcastAlwaysDelivers raw p
    --  {-by def of broadcast-}                     === (let _m = broadcastHelper_prepareMessage raw p
    --                                                       _p = broadcastHelper_injectMessage _m p
    --                                                       Just (__m, __p) = deliver _p in __p)
    --  {-by composition of functions-}             === (let _p = broadcastHelper_injectMessage (broadcastHelper_prepareMessage raw p) p
    --                                                       Just (__m, __p) = deliver _p in __p)
    --  {-by def of broadcastPrepareInjectShim-}    === (let _p = broadcastPrepareInjectShim raw p
    --                                                       Just (__m, __p) = deliver _p in __p)
        {-by def of p'-}                            === (let Just (__m, __p) = deliver p' in __p)

--  in
--  deliverPLCDpres n p' -- p'PLCD to p''PLCD
--      (broadcastPrepareInjectCHApres raw n p pCHA) -- pCHA to p'CHA
--      (broadcastPrepareInjectPLCDpres raw n p pCHA pPLCD) -- pPLCD to p'PLCD
--      ? broadcastBody
--      -- ∀ m m'

    -- convert evidence from p to p'
    p'CHA = broadcastPrepareInjectCHApres raw n p pCHA
    p'PLCD = broadcastPrepareInjectPLCDpres raw n p pCHA pPLCD -- ∀ m m'
    -- convert evidence from p' to p''
    p''PLCD = deliverPLCDpres n p' p'CHA p'PLCD -- ∀ m m'
    in
    (p''PLCD ? broadcastBody) -- ∀ m m'
