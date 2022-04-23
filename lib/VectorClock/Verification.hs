{-# OPTIONS_GHC "-Wno-warnings-deprecations" #-} -- Hide the "verification only" and "internal use" warnings

-- | Proofs about vector clock relation and operator properties.
module VectorClock.Verification {-# WARNING "Verification only" #-} where

import Language.Haskell.Liquid.ProofCombinators
import Language.Haskell.Liquid.Properties

import Redefined
import VectorClock

-- TODO: vcTick properties




-- * vcLessEqual non-strict partial order

{-@
vcLessEqualReflexiveNoPLE :: Reflexive VC {vcLessEqual} @-}
vcLessEqualReflexiveNoPLE :: VC -> Proof
vcLessEqualReflexiveNoPLE []
    =   vcLessEqual [] []
    === listAnd (listZipWith vcLessEqualHelper [] [])
    === listAnd []
    === True
    *** QED
vcLessEqualReflexiveNoPLE (x:xs)
    =   vcLessEqual (x:xs) (x:xs)
    === listAnd (listZipWith vcLessEqualHelper (x:xs) (x:xs))
    === listAnd (vcLessEqualHelper x x : listZipWith vcLessEqualHelper xs xs)
    === (vcLessEqualHelper x x && (listAnd (listZipWith vcLessEqualHelper xs xs)))
    === ((x <= x) && (listAnd (listZipWith vcLessEqualHelper xs xs)))
    === (True && (listAnd (listZipWith vcLessEqualHelper xs xs)))
    === listAnd (listZipWith vcLessEqualHelper xs xs)
    === vcLessEqual xs xs
        ? vcLessEqualReflexiveNoPLE xs
    === True
    *** QED

{-@ ple vcLessEqualReflexive @-}
{-@
vcLessEqualReflexive :: Reflexive VC {vcLessEqual} @-}
vcLessEqualReflexive :: VC -> Proof
vcLessEqualReflexive [] = ()
vcLessEqualReflexive (_x:xs) = vcLessEqualReflexive xs

{-@ ple vcLessEqualTransitive @-}
{-@
vcLessEqualTransitive :: n:Nat -> Transitive (VCsized {n}) {vcLessEqual} @-}
vcLessEqualTransitive :: Int -> VC -> VC -> VC -> Proof
vcLessEqualTransitive _n [] [] [] = ()
vcLessEqualTransitive n (_x:xs) (_y:ys) (_z:zs) = vcLessEqualTransitive (n - 1) xs ys zs

{-@ ple vcLessEqualAntisymmetric @-}
{-@
vcLessEqualAntisymmetric :: n:Nat -> Antisymmetric (VCsized {n}) {vcLessEqual} @-}
vcLessEqualAntisymmetric :: Int -> VC -> VC -> Proof
vcLessEqualAntisymmetric _n [] [] = ()
vcLessEqualAntisymmetric n (_x:xs) (_y:ys) = vcLessEqualAntisymmetric (n - 1) xs ys




-- * vcLess strict partial order

{-@ ple vcLessIrreflexive @-}
{-@
vcLessIrreflexive :: Irreflexive VC {vcLess} @-}
vcLessIrreflexive :: VC -> Proof
vcLessIrreflexive [] = ()
vcLessIrreflexive (_x:xs) = vcLessIrreflexive xs

{-@ ple vcLessTransitive @-}
{-@
vcLessTransitive :: n:Nat -> Transitive (VCsized {n}) {vcLess} @-}
vcLessTransitive :: Int -> VC -> VC -> VC -> Proof
vcLessTransitive _n [] [] [] = ()
vcLessTransitive n (_x:xs) (_y:ys) (_z:zs)
    -- since the tails are nonequal, rely on the inductive assumption
    | xs /= ys && ys /= zs = vcLessTransitive (n - 1) xs ys zs
    -- since the tails might be equal, base case
    | otherwise = ()

{-@ ple vcLessAntisymmetric @-}
{-@
vcLessAntisymmetric :: n:Nat -> Antisymmetric (VCsized {n}) {vcLess} @-}
vcLessAntisymmetric :: Int -> VC -> VC -> Proof
vcLessAntisymmetric _n [] [] = ()
vcLessAntisymmetric n (_x:xs) (_y:ys) = vcLessAntisymmetric (n - 1) xs ys

{-@
vcLessAsymmetric :: n:Nat -> Asymmetric (VCsized {n}) {vcLess} @-}
vcLessAsymmetric :: Int -> VC -> VC -> Proof
vcLessAsymmetric n =
    irreflexiveAntisymmetric vcLess vcLessIrreflexive (vcLessAntisymmetric n)




-- * vcConcurrent reflexive & symmetric

{-@ ple vcConcurrentReflexive @-}
{-@
vcConcurrentReflexive :: Reflexive VC {vcConcurrent} @-}
vcConcurrentReflexive :: VC -> Proof
vcConcurrentReflexive [] = ()
vcConcurrentReflexive (_x:xs) = vcConcurrentReflexive xs

{-@ ple vcConcurrentSymmetric @-}
{-@
vcConcurrentSymmetric :: n:Nat -> Symmetric (VCsized {n}) {vcConcurrent} @-}
vcConcurrentSymmetric :: Int -> VC -> VC -> Proof
vcConcurrentSymmetric _n _xs _ys = ()




-- * vcCombine & vcLessEqual properties

-- | TODO: prove this generally for anything which is commutative and has mono-right
{-@ ple vcCombineVCLessEqualMonotonicLeft @-}
{-@
vcCombineVCLessEqualMonotonicLeft :: n:Nat -> MonotonicLeft (VCsized {n}) {vcLessEqual} {vcCombine} @-}
vcCombineVCLessEqualMonotonicLeft :: Int -> VC -> VC -> VC -> Proof
vcCombineVCLessEqualMonotonicLeft _n [] [] [] = ()
vcCombineVCLessEqualMonotonicLeft n (_x:xs) (_y:ys) (_k:ks) =
    vcCombineVCLessEqualMonotonicLeft (n - 1) xs ys ks

-- | TODO: prove this generally for anything which is commutative and has mono-left
{-@ ple vcCombineVCLessEqualMonotonicRight @-}
{-@
vcCombineVCLessEqualMonotonicRight :: n:Nat -> MonotonicRight (VCsized {n}) {vcLessEqual} {vcCombine} @-}
vcCombineVCLessEqualMonotonicRight :: Int -> VC -> VC -> VC -> Proof
vcCombineVCLessEqualMonotonicRight _n [] [] [] = ()
vcCombineVCLessEqualMonotonicRight n (_k:ks) (_x:xs) (_y:ys) =
    vcCombineVCLessEqualMonotonicRight (n - 1) ks xs ys

-- | TODO: prove this generally for anything which has mono-left and mono-right
{-@ ple vcCombineVCLessEqualMonotonic @-}
{-@
vcCombineVCLessEqualMonotonic :: n:Nat -> Monotonic (VCsized {n}) {vcLessEqual} {vcCombine} @-}
vcCombineVCLessEqualMonotonic :: Int -> VC -> VC -> VC -> VC -> Proof
vcCombineVCLessEqualMonotonic _n [] [] [] [] = ()
vcCombineVCLessEqualMonotonic n (_a:as) (_b:bs) (_x:xs) (_y:ys) =
    vcCombineVCLessEqualMonotonic (n - 1) as bs xs ys




-- * vcCombine properties

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

{-@ ple vcCombineResultLarger @-}
{-@
vcCombineResultLarger :: a:VC -> b:VCasV {a} -> { vcLessEqual a (vcCombine a b)
                                               && vcLessEqual b (vcCombine a b) } @-}
vcCombineResultLarger :: VC -> VC -> Proof
vcCombineResultLarger [] []
    {-restate conclusion-}      =   vcCombine [] []
    {-by def of vcCombine-}     === listZipWith ordMax [] []
    {-by def of listZipWith-}   === []
    ? vcLessEqualReflexive []   *** QED
vcCombineResultLarger (x:xs) (y:ys)
    {-restate (half of) conclusion-}    =   vcLessEqual (x:xs) ret
    {-by def of listAnd,zipWith,etc-}   === (x <= (if x < y then y else x) && listAnd (listZipWith vcLessEqualHelper xs (vcCombine xs ys)))
    ? vcCombineResultLarger xs ys       === (x <= (if x < y then y else x))
    {-vcCombineAssociativity-}          *** QED
  where
    ret =   vcCombine (x:xs) (y:ys)
        === listZipWith ordMax (x:xs) (y:ys)
        === ordMax x y : listZipWith ordMax xs ys
        === (if x < y then y else x) : listZipWith ordMax xs ys
