{-# OPTIONS_GHC "-Wno-unused-imports" #-} -- LH needs bodies of reflected definitions
{-# OPTIONS_GHC "-Wno-warnings-deprecations" #-} -- Hide the "verification only" and "internal use" warnings
{-# LANGUAGE GADTs #-}

-- | Permissive network-semantics for executions running CBCAST.
module CBCAST.Verification.Global.Step {-# WARNING "Verification only" #-} where

import Prelude hiding (foldr, uncurry)

-- import Redefined
import CBCAST.Core
import CBCAST.Step
import CBCAST.Verification.PLCDpresStep (stepShim)
import CBCAST.Verification.Global.Core
-- import CBCAST.Transitions




-- * Step-relation for executions

-- | Minimum-viable network-semantics. It selects an operation and applies it
-- to a process in an execution. There are no constraints, so a random or
-- pathological message can pop into the universe and be received by a process.
{-@
xStep :: n:Nat -> OPsized r {n} -> PIDsized {n} -> Xsized r {n} -> Xsized r {n} @-}
xStep :: Int -> Op r -> PID -> Execution r -> Execution r
xStep n op pid x₀ = -- setProcess2 n (stepShim op (x pid)) x
    let p₀ = x₀ pid
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

{-@
foldr_xStep :: n:Nat -> Xsized r {n} -> [(OPsized r {n}, PIDsized {n})] -> Xsized r {n} @-}
foldr_xStep :: Int -> Execution r -> [(Op r, PID)] -> Execution r
foldr_xStep n x = foldr (uncurry (xStep n)) x
{-@ reflect foldr_xStep @-}
