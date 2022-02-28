{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}
{-# OPTIONS_GHC "-Wno-unused-imports" #-} -- LH needs Redefined.Ord
module Properties2 where

import Language.Haskell.Liquid.ProofCombinators
import Redefined.Ord

import SystemModel
import Properties ()
import UCausalDelivery

{-@ ple vcCombineAssociativity @-}
{-@
vcCombineAssociativity :: n:Nat -> Associative (VCsized {n}) {vcCombine} @-}
vcCombineAssociativity :: Int -> VC -> VC -> VC -> Proof
vcCombineAssociativity _n [] [] [] = ()
vcCombineAssociativity n (_x:xs) (_y:ys) (_z:zs) = vcCombineAssociativity (n - 1) xs ys zs

{-@ ple vcCombineCommutativity @-}
{-@
vcCombineCommutativity :: n:Nat -> Commutative (VCsized {n}) {vcCombine} @-}
vcCombineCommutativity :: Int -> VC -> VC -> Proof
vcCombineCommutativity _n [] [] = ()
vcCombineCommutativity n (_x:xs) (_y:ys) = vcCombineCommutativity (n - 1) xs ys

{-@ ple vcCombineIdempotence @-}
{-@
vcCombineIdempotence :: a:VC -> {a == vcCombine a a} @-}
vcCombineIdempotence :: VC -> Proof
vcCombineIdempotence [] = ()
vcCombineIdempotence (_x:xs) = vcCombineIdempotence xs

{-@ ple vcCombineVCLessEqualMonotonicLeft @-}
{-@
vcCombineVCLessEqualMonotonicLeft :: n:Nat -> MonotonicLeft (VCsized {n}) {vcLessEqual} {vcCombine} @-}
vcCombineVCLessEqualMonotonicLeft :: Int -> VC -> VC -> VC -> Proof
vcCombineVCLessEqualMonotonicLeft _n [] [] [] = ()
vcCombineVCLessEqualMonotonicLeft n (_x:xs) (_y:ys) (_k:ks) =
    vcCombineVCLessEqualMonotonicLeft (n - 1) xs ys ks

{-@ ple vcCombineVCLessEqualMonotonicRight @-}
{-@
vcCombineVCLessEqualMonotonicRight :: n:Nat -> MonotonicRight (VCsized {n}) {vcLessEqual} {vcCombine} @-}
vcCombineVCLessEqualMonotonicRight :: Int -> VC -> VC -> VC -> Proof
vcCombineVCLessEqualMonotonicRight _n [] [] [] = ()
vcCombineVCLessEqualMonotonicRight n (_k:ks) (_x:xs) (_y:ys) =
    vcCombineVCLessEqualMonotonicRight (n - 1) ks xs ys

{-@ ple vcCombineVCLessEqualMonotonic @-}
{-@
vcCombineVCLessEqualMonotonic :: n:Nat -> Monotonic (VCsized {n}) {vcLessEqual} {vcCombine} @-}
vcCombineVCLessEqualMonotonic :: Int -> VC -> VC -> VC -> VC -> Proof
vcCombineVCLessEqualMonotonic _n [] [] [] [] = ()
vcCombineVCLessEqualMonotonic n (_a:as) (_b:bs) (_x:xs) (_y:ys) =
    vcCombineVCLessEqualMonotonic (n - 1) as bs xs ys
