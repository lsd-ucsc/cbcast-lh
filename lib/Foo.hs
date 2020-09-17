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
