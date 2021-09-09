module Redefined.Function where

-- $setup
-- >>> :set -XFlexibleInstances
-- >>> instance Show (a -> b) where show _ = "(a -> b)"

-- | Implementation of 'flip' lifted to specifications. Probably same as
-- 'Prelude'.
--
-- prop> f a b == flip f b a && flip f b a == funFlip f b a
{-@ reflect funFlip @-}
funFlip :: (a -> b -> c) -> b -> a -> c
funFlip f b a = f a b
