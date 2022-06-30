{-# OPTIONS_GHC "-Wno-unused-imports" #-} -- LH needs bodies of reflected definitions
{-# OPTIONS_GHC "-Wno-warnings-deprecations" #-} -- Hide the "verification only" and "internal use" warnings

module CBCAST.Verification.PLCDpresStep {-# WARNING "Verification only" #-} where

import Prelude hiding (foldr)

import Language.Haskell.Liquid.ProofCombinators (Proof, (===), (***), QED(..), (?))

import Redefined
import VectorClock
import CBCAST.Core
import CBCAST.Transitions
import CBCAST.Step
import CBCAST.Verification.ProcessOrder
import CBCAST.Verification.Shims
import CBCAST.Verification.PLCDpres
import CBCAST.Verification.PLCDpresDeliver
import CBCAST.Verification.PLCDpresBroadcast




-- * PLCD preservation of Step

{-@
stepPLCDpres :: op:Op r -> PLCDpreservation r {opSize op} {stepShim op} @-}
stepPLCDpres :: Eq r => Op r -> Process r -> (Message r -> Message r -> Proof)
                                          -> (Message r -> Message r -> Proof)
stepPLCDpres op p pPLCD = -- ∀ m m'
  case op of
    OpReceive   n m -> receivePLCDpres   m   p pPLCD ? (step op p === ResultReceive   n (internalReceive   m p))
    OpDeliver   n   -> deliverPLCDpres     n p pPLCD ? (step op p === ResultDeliver   n (internalDeliver     p))
    OpBroadcast n r -> broadcastPLCDpres r n p pPLCD ? (step op p === ResultBroadcast n (internalBroadcast r p))




-- * PLCD preservation of Step TRC

---- foldr :: (a -> b -> b) -> b -> [a] -> b
---- foldr f acc (x:xs) = f x (foldr f acc xs)
---- foldr _ acc [] = acc
---- {-@ reflect foldr @-}
---- 
---- -- QQQ: Why can't we use this @foldr@ with @step@?
---- --
---- -- The inferred type
---- --   VV : (CBCAST.Core.Process a)
---- -- .
---- -- is not a subtype of the required type
---- --   VV : {VV : (CBCAST.Core.Process a) | listLength (pVC VV) == opSize ?a}
---- --
---- {-@
---- foldr_step :: p:Process r -> [OPasP r {p}] -> PasP r {p} @-}
---- foldr_step :: Process r -> [Op r] -> Process r
---- foldr_step p ops = foldr stepShim p ops

-- | Transitive Reflexive Closure of step(Shim).
--
-- This is @foldr@ with @step@ inlined, such that instead of @foldr@ taking an
-- argument, the body of @foldr@ is defined with @step@ inside.
{-@
foldr_step :: p:Process r -> [OPasP r {p}] -> PasP r {p} @-}
foldr_step :: Process r -> [Op r] -> Process r
foldr_step acc (x:xs) = stepShim x (foldr_step acc xs)
foldr_step acc [] = acc
{-@ reflect foldr_step @-}

flip :: (a -> b -> c) -> b -> a -> c
flip f b a = f a b
{-@ inline flip @-}

-- | The transitive reflexive closure of step(Shim) preserves PLCD.
{-@
trcPLCDpres
    ::   n : Nat
    -> ops : [OPsized r {n}]
    -> PLCDpreservation r {n} {flip foldr_step ops}
@-}
trcPLCDpres :: Eq r => Int -> [Op r] -> Process r -> (Message r -> Message r -> Proof)
                                                  -> (Message r -> Message r -> Proof)
trcPLCDpres _n [] p pPLCD = -- ∀ m m'
    pPLCD -- ∀ m m'
    ? (foldr_step p [] === p) -- p is unchanged
trcPLCDpres n (op:ops) p pPLCD =
    let
    prev = foldr_step p ops
    prevPLCD = trcPLCDpres n ops p pPLCD
    in
    stepPLCDpres op prev prevPLCD -- ∀ m m'
    ? (foldr_step p (op:ops) === stepShim op (foldr_step p ops))
