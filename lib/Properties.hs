{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}
-- {-# LANGUAGE NoFieldSelectors #-}
{-# LANGUAGE NamedFieldPuns #-}
module Properties where


import Language.Haskell.Liquid.ProofCombinators
import SystemModel

{-@ type   Reflexive a R = x:a -> {R x x} @-}
{-@ type Irreflexive a R = x:a -> {not (R x x)} @-}

{-@ type     Symmetric a R = x:a -> {y:a | R x y} -> {R y x} @-}
{-@ type    Asymmetric a R = x:a -> {y:a | R x y} -> {not (R y x)} @-}
{-@ type Antisymmetric a R = x:a -> {y:a | R x y && R y x} -> {x == y} @-}

{-@ type Transitive a R = x:a -> {y:a | R x y} -> {z:a | R y z} -> {R x z} @-}
{-@ type Total a R = x:a -> y:a -> {(R x y || R y x) && not (R x y && R y x)} @-}

-- Preorder                  : Transitive, Reflexive
-- Partial order (non-strict): Transitive, Reflexive, Antisymmetric
-- Total order               : Transitive, Reflexive, Antisymmetric, Total
-- Partial order (strict)    : Transitive, (ONE-OF: Irreflexive, Asymmetric)
-- Equivalence               : Transitive, Reflexive, Symmetric




-- * Generic properties

-- | Irreflexive and Antisymmetric imply Asymmetric.
--
--   ( ∀ x. ¬xRx )
-- ∧ ( ∀ x y. xRy ∧ yRx → x≡y )
-- ⇒
--   ( ∀ x y. xRy → ¬yRx )
{-@
irreflexiveAntisymmetric :: r:_ -> Irreflexive a {r} -> Antisymmetric a {r} -> Asymmetric a {r} @-}
irreflexiveAntisymmetric :: Eq a => (a -> a -> Bool) -> (a -> Proof) -> (a -> a -> Proof) -> (a -> a -> Proof)
irreflexiveAntisymmetric r irrefl antisym x y
    | r x y && r y x
        =   x ? antisym x y
        === y ? irrefl y
        --- `x == y && not (r y y)` contradicts the case assumption
        *** QED
    | otherwise
        = () -- assumed the conclusion `not (r a b)` or the reverse




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

{-@ ple vcLessEqualAntiSymmetric @-}
{-@
vcLessEqualAntiSymmetric :: n:Nat -> Antisymmetric (VCsized {n}) {vcLessEqual} @-}
vcLessEqualAntiSymmetric :: Int -> VC -> VC -> Proof
vcLessEqualAntiSymmetric _n [] [] = ()
vcLessEqualAntiSymmetric n (_x:xs) (_y:ys) = vcLessEqualAntiSymmetric (n - 1) xs ys




-- * vcLess strict partial order

{-@ ple vcLessIrreflexive @-}
{-@
vcLessIrreflexive :: Irreflexive VC {vcLess} @-}
vcLessIrreflexive :: VC -> Proof
vcLessIrreflexive [] = ()
vcLessIrreflexive (_x:xs) = vcLessIrreflexive xs

-- {-@ ple vcLessTransitive @-}
-- {-@
-- vcLessTransitive :: n:Nat -> Transitive (VCsized {n}) {vcLess} @-}
-- vcLessTransitive :: Int -> VC -> VC -> VC -> Proof
-- vcLessTransitive _n [] [] [] = ()
-- vcLessTransitive n (_x:xs) (_y:ys) (_z:zs) = vcLessTransitive (n - 1) xs ys zs

{-@ ple vcLessAntiSymmetric @-}
{-@
vcLessAntiSymmetric :: n:Nat -> Antisymmetric (VCsized {n}) {vcLess} @-}
vcLessAntiSymmetric :: Int -> VC -> VC -> Proof
vcLessAntiSymmetric _n [] [] = ()
vcLessAntiSymmetric n (_x:xs) (_y:ys) = vcLessAntiSymmetric (n - 1) xs ys

-- | TODO prove this using the fact that it's irreflexive and antisymmetric?
-- {-@ ple vcLessAsymmetric @-}
-- {-@
-- vcLessAsymmetric :: n:Nat -> Asymmetric (VCsized {n}) {vcLess} @-}
-- vcLessAsymmetric :: Int -> VC -> VC -> Proof
-- vcLessAsymmetric _n [] [] = ()
-- vcLessAsymmetric n (_x:xs) (_y:ys) = vcLessAsymmetric (n - 1) xs ys



-- * vcConcurrent reflexive & symmetric

{-@ ple vcConcurrentReflexive @-}
{-@
vcConcurrentReflexive :: Reflexive VC {vcConcurrent} @-}
vcConcurrentReflexive :: VC -> Proof
vcConcurrentReflexive [] = ()
vcConcurrentReflexive (_x:xs) = vcConcurrentReflexive xs

-- {-@ ple vcConcurrentSymmetric @-}
-- {-@
-- vcConcurrentSymmetric :: n:Nat -> Symmetric (VCsized {n}) {vcConcurrent} @-}
-- vcConcurrentSymmetric :: Int -> VC -> VC -> Proof
-- vcConcurrentSymmetric _n [] [] = ()
-- vcConcurrentSymmetric n (_x:xs) (_y:ys) = vcConcurrentSymmetric (n - 1) xs ys
