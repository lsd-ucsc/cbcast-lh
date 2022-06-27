{-# OPTIONS_GHC "-Wno-unused-imports" #-} -- LH needs bodies of reflected definitions
{-# OPTIONS_GHC "-Wno-warnings-deprecations" #-} -- Hide the "verification only" and "internal use" warnings
{-# LANGUAGE GADTs #-}

module CBCAST.Verification.NetworkSemantics2 {-# WARNING "Verification only" #-} where

import Prelude hiding (foldr, uncurry)

import Redefined
import CBCAST.Core
import CBCAST.Step
import CBCAST.Transitions
import CBCAST.Verification.PLCDpresStep (stepShim)




-- * Execution

-- | An execution is a mapping from process identifier to CBCAST processes. The
-- mapping is constrained to only those processes /in/ the execution by the
-- size parameter, @N@.
type Execution r = PID -> Process r
{-@ type Xsized r N = p_id_k:PIDsized {N} -> {p_v:Psized r {N} | p_id_k == pID p_v} @-}

{-@
setProcess :: n:Nat -> p_id:PIDsized {n} -> {p:Psized r {n} | p_id == pID p} -> Xsized r {n} -> Xsized r {n} @-}
setProcess :: Int -> PID -> Process r -> Execution r -> Execution r
setProcess _n k v mapping target
    | target == k = v
    | otherwise = mapping target
{-@ reflect setProcess @-}

{-@
setProcess2 :: n:Nat -> Psized r {n} -> Xsized r {n} -> Xsized r {n} @-}
setProcess2 :: Int -> Process r -> Execution r -> Execution r
setProcess2 n p = setProcess n (pID p) p
{-@ reflect setProcess2 @-}




-- * Step-relation for executions

{-@
xStep :: n:Nat -> OPsized r {n} -> PIDsized {n} -> Xsized r {n} -> Xsized r {n} @-}
xStep :: Int -> Op r -> PID -> Execution r -> Execution r
xStep n op pid x₀ = -- setProcess2 n (stepShim op (x pid)) x
    let p₀ = x₀ pid
        p₁ = stepShim op p₀
        x₁ = setProcess2 n p₁ x₀
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



