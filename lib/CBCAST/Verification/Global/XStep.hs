{-# OPTIONS_GHC "-Wno-unused-imports" #-} -- LH needs bodies of reflected definitions
{-# OPTIONS_GHC "-Wno-warnings-deprecations" #-} -- Hide the "verification only" and "internal use" warnings
{-# LANGUAGE GADTs #-}

-- | Permissive network-semantics for executions running CBCAST.
module CBCAST.Verification.Global.XStep {-# WARNING "Verification only" #-} where

import Prelude hiding (foldr, uncurry)
import Language.Haskell.Liquid.ProofCombinators

-- import Redefined
import CBCAST.Core
import CBCAST.Step
import CBCAST.Verification.Shims
import CBCAST.Verification.Global.Core
-- import CBCAST.Transitions




-- * Step-relation for executions

-- | Minimum-viable network-semantics. It selects an operation and applies it
-- to a process in an execution. There are no constraints, so a random or
-- pathological message can pop into the universe and be received by a process.
{-@
xStep :: n:Nat -> OPsized r {n} -> PIDsized {n} -> Xsized r {n} -> Xsized r {n} @-}
xStep :: Int -> Op r -> PID -> Execution r -> Execution r
xStep n op p_id x₀ = -- xSetProc n (stepShim op (x₀ p_id)) x₀
    let p₀ = x₀ p_id
        p₁ = stepShim op p₀
        x₁ = xSetProc n p₁ x₀
    in x₁
{-@ reflect xStep @-}




-- * TRC for stepping executions

foldr :: (a -> b -> b) -> b -> [a] -> b
foldr f acc (x:xs) = f x (foldr f acc xs)
foldr _ acc [] = acc
{-@ reflect foldr @-}

uncurry :: (a -> b -> c) -> (a, b) -> c
uncurry f (a, b) = f a b
{-@ reflect uncurry @-}

flip' :: (a -> b -> c) -> b -> a -> c
flip' f b a = f a b
{-@ reflect flip' @-}

-- ** Lemmas

{-@ flip'Apply :: f:(a -> b -> c) -> b:b -> a:a -> { flip' f b a == f a b } @-}
flip'Apply :: (a -> b -> c) -> b -> a -> Proof
flip'Apply _ _ _ = () {-@ ple flip'Apply @-}

{-@ uncurryApply :: f:(a -> b -> c) -> v:(a, b) -> { uncurry f v == f (fst v) (snd v) } @-}
uncurryApply :: (a -> b -> c) -> (a, b) -> Proof
uncurryApply _ (_,_) = () {-@ ple uncurryApply @-}

{-@
foldrPenultimate
    ::        f : (a -> b -> b)
    ->        v :  a
    ->       vs : [a]
    ->    first :  b
    -> { penult :  b  | penult == foldr f first         vs  }
    -> {   last :  b  |   last == foldr f first (cons v vs) }
    -> { f v penult == last }
@-}
foldrPenultimate :: (a -> b -> b) -> a -> [a] -> b -> b -> b -> Proof
foldrPenultimate _f _v _vs _first _penult _last = () {-@ ple foldrPenultimate @-}

{-@
foldrEmpty
    ::     f : (a -> b -> b)
    -> first : b
    -> { first == foldr f first [] }
@-}
foldrEmpty :: (a -> b -> b) -> b -> Proof
foldrEmpty _f _first = () {-@ ple foldrEmpty @-}

-- ** TRC

-- | Transitive Reflexive Closure of xStep.
--
-- NOTE: We don't use this binder in proofs. We use the body. Why? Because our
-- executions are defined as functions, and so we cannot compare them for
-- equality. As a workaround we abstract out the reasoning about equality on
-- executions to proofs that reason about equality of a type parameter.  To use
-- such proofs result requires that we never "expand" a definition like
-- @foldr_xStep@.
{-@
foldr_xStep :: n:Nat -> [(OPsized r {n}, PIDsized {n})] -> Xsized r {n} -> Xsized r {n} @-}
foldr_xStep :: Int -> [(Op r, PID)] -> Execution r -> Execution r
foldr_xStep n ops x = flip' (foldr (uncurry (xStep n))) ops x
