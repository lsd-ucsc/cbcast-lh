{-# LANGUAGE QuasiQuotes #-}
module UseOfEgQQ where

import LiquidHaskell (lq)
import Eg

[lq| measure twoListSize |]
twoListSize :: ([a], [b]) -> Int
twoListSize (as, bs) = listSize as + listSize bs
