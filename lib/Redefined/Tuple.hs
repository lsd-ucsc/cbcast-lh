module Redefined.Tuple where

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
