module Redefined.Fin where

-- * Agda things reimplemented

-- | A member of a finite set of natural numbers.
{-@ type Fin V = {k:Nat | k < V} @-}
type Fin = Int

{-@ reflect fin @-}
{-@ fin :: n:Nat -> FinDesc {n} @-}
fin :: Int -> [Int]
fin = finDesc
{-# DEPRECATED fin "renamed to finDesc" #-}

{-@ type FinDesc N = {xs:[Fin {N}]<{\a b -> a > b}> | len xs == N} @-}
{-@ type FinAsc  N = {xs:[Fin {N}]<{\a b -> a < b}> | len xs == N} @-}

-- | Generate the elements of a finite set @Fin n@ in descending order
--
-- >>> finDesc (-1)
-- []
-- >>> finDesc 0
-- []
-- >>> finDesc 1
-- [0]
-- >>> finDesc 2
-- [1,0]
-- >>> finDesc 3
-- [2,1,0]
--
{-@ finDesc :: n:Nat -> FinDesc {n} @-}
finDesc :: Int -> [Int]
finDesc k = let k' = k - 1 in if 0 <= k' then k' : finDesc k' else []
{-@ reflect finDesc @-}

-- | Generate the elements of a finite set @Fin n@ in ascending order
--
-- >>> finAsc (-1)
-- []
-- >>> finAsc 0
-- []
-- >>> finAsc 1
-- [0]
-- >>> finAsc 2
-- [0,1]
-- >>> finAsc 3
-- [0,1,2]
--
{-@ finAsc :: n:Nat -> FinAsc {n} @-}
finAsc :: Int -> [Int]
finAsc n = finAscHelper 0 n
{-@ reflect finAsc @-}

-- | Returns bounded by [m..n) in ascending order.
--
-- >>> finAscHelper 4 9
-- [4,5,6,7,8]
--
{-@ finAscHelper
        ::  m:Nat
        -> {n:Nat | m <= n}
        -> {xs:[{x:_ | m <= x && x < n}]<{\a b -> a < b}> | len xs == n-m}
        / [n-m] @-}
finAscHelper :: Int -> Int -> [Int]
finAscHelper m n =
    if m < n
    then m : finAscHelper (m+1) n
    else []
{-@ reflect finAscHelper @-}
