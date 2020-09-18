{-# LANGUAGE QuasiQuotes #-}
module Foo where

import LiquidHaskell (lq)

[lq| type TRUE = {v:Bool | v = True} |]

-- |
--
-- >>> x
-- True
[lq| x :: TRUE |]
x = not False

[lq| type Nat = {v:Int | 0 <= v} |]

[lq| bar :: {n:Nat | n < 10} |]
bar = 2

class Foo a where
    foo :: a -> Int
{-@ foo :: a -> {n:Nat | n < 10} @-}

instance Foo Bool where
    foo True = 1
    foo False = 11
