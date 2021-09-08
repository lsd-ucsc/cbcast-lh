module Redefined.Tuple where

-- $setup
--
-- >>> import Data.Tuple

-- |
--
-- prop> fst t == tupleFirst t
{-@ reflect tupleFirst @-}
tupleFirst :: (a, b) -> a
tupleFirst (a, _b) = a

-- |
--
-- prop> snd t == tupleSecond t
{-@ reflect tupleSecond @-}
tupleSecond :: (a, b) -> b
tupleSecond (_a, b) = b

-- |
--
-- prop> swap t == tupleSwap t
{-@ reflect tupleSwap @-}
tupleSwap :: (a, b) -> (b, a)
tupleSwap (a, b) = (b, a)

-- * Functions that don't exist in prelude

{-@ reflect firstEquals @-}
firstEquals :: Eq a => a -> (a, b) -> Bool
firstEquals a' (a, _b) = a' == a

{-@ reflect secondEquals @-}
secondEquals :: Eq b => b -> (a, b) -> Bool
secondEquals b' (_a, b) = b' == b
