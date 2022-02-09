{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}
{-# OPTIONS_GHC "-Wno-unused-imports" #-} -- LH needs Redefined.Ord
module Properties2 where

import Language.Haskell.Liquid.ProofCombinators
import Redefined.Ord

import SystemModel
import Properties ()
import UCausalDelivery

{-@ ple vcCombineVCLessEqualMonotonicLeft @-}
{-@
vcCombineVCLessEqualMonotonicLeft :: n:Nat -> MonotonicLeft (VCsized {n}) {vcLessEqual} {vcCombine} @-}
vcCombineVCLessEqualMonotonicLeft :: Int -> VC -> VC -> VC -> Proof
vcCombineVCLessEqualMonotonicLeft _n [] [] [] = ()
vcCombineVCLessEqualMonotonicLeft n (_x:xs) (_y:ys) (_k:ks) =
    vcCombineVCLessEqualMonotonicLeft (n - 1) xs ys ks
