-- |
--
-- These are definitions redefined from elsewhere for use with LiquidHaskell.
module Redefined
( module Redefined
, module X
) where

import Redefined.List as X
import Redefined.Fin as X
import Redefined.Set as X

-- $setup
-- >>> :set -XFlexibleInstances
-- >>> instance Show (a -> b) where show _ = "(a -> b)"

-- * Haskell things reimplemented

{-@ reflect boolAnd @-}
{-@ boolAnd :: a:Bool -> b:Bool -> {c:Bool | c <=> a && b} @-}
boolAnd :: Bool -> Bool -> Bool
boolAnd True True = True
boolAnd _ _ = False

-- | Implementation of 'flip' lifted to specifications. Probably same as
-- 'Prelude'.
--
-- prop> f a b == flip f b a && flip f b a == funFlip f b a
{-@ reflect funFlip @-}
funFlip :: (a -> b -> c) -> b -> a -> c
funFlip f b a = f a b

-- | Implementation of 'impossible' lifted to specifications. similar to the
-- one in 'Language.Haskell.Liquid.ProofCombinators'.
{-@ inline impossibleConst @-}
{-@ impossibleConst :: a -> {v:b | false } -> a @-}
impossibleConst :: a -> b -> a
impossibleConst a _ = a

{-@ inline proofConst @-}
proofConst :: a -> b -> a
proofConst x _ = x

-- * Agda things reimplemented

-- | A list of fixed size.
{-@ type Vec a V = {v:[a] | len v == V} @-}
type Vec a = [a]
