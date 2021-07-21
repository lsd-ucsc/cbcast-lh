module Redefined.Fin where

-- * Agda things reimplemented

-- | A member of a finite set of natural numbers.
{-@ type Fin V = {k:Nat | k < V} @-}
type Fin = Int

-- | Generate the elements of a finite set @Fin n@.
--
-- >>> fin (-1)
-- []
-- >>> fin 0
-- []
-- >>> fin 1
-- [0]
-- >>> fin 2
-- [1,0]
--
{-@ reflect fin @-}
{-@ fin :: v:Nat -> {xs:[Fin {v}]<{\a b -> a > b}> | len xs == v} @-}
fin :: Int -> [Int]
fin k = let k' = k - 1 in if 0 < k then k' : fin k' else []
