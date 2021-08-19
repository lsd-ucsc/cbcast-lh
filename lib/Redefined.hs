-- |
--
-- These are definitions redefined from elsewhere for use with LiquidHaskell.
module Redefined
( module Redefined
, module X
) where

import Redefined.Bool as X
import Redefined.Tuple as X
import Redefined.List as X
import Redefined.Fin as X
import Redefined.Set as X

-- $setup
-- >>> :set -XFlexibleInstances
-- >>> instance Show (a -> b) where show _ = "(a -> b)"

-- * Haskell things reimplemented

-- | Implementation of 'flip' lifted to specifications. Probably same as
-- 'Prelude'.
--
-- prop> f a b == flip f b a && flip f b a == funFlip f b a
{-@ reflect funFlip @-}
funFlip :: (a -> b -> c) -> b -> a -> c
funFlip f b a = f a b

-- * LiquidHaskell proof-combinators reimplemented

-- | Implementation of 'impossible' lifted to specifications. similar to the
-- one in 'Language.Haskell.Liquid.ProofCombinators'.
{-@ inline impossibleConst @-}
{-@ impossibleConst :: a -> {v:b | false } -> a @-}
impossibleConst :: a -> b -> a
impossibleConst a _ = a

{-@ inline proofConst @-}
proofConst :: a -> b -> a
proofConst x _ = x

-- * Racket things reimplemented

{-@ reflect listAndMap @-}
listAndMap :: (a -> Bool) -> [a] -> Bool
listAndMap f xs = listAnd (listMap f xs)

{-@ reflect listOrMap @-}
listOrMap :: (a -> Bool) -> [a] -> Bool
listOrMap f xs = listOr (listMap f xs)

-- * Agda things reimplemented

-- | A list of fixed size.
{-@ type Vec a V = {v:[a] | len v == V} @-}
type Vec a = [a]
