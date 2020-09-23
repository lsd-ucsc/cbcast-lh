{-# LANGUAGE QuasiQuotes #-}
module EgQQ where

import LiquidHaskell (lq)

[lq| measure listSize |]
listSize :: [a] -> Int
listSize [] = 0
listSize (_x:xs) = 1 + listSize xs
