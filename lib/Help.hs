{-# LANGUAGE QuasiQuotes #-}
module Help where

import LiquidHaskell (lq)

{-@
len :: [a] -> Int @-}
len :: [a] -> Int
len [] = 0
len (_x:xs) = 1 + len xs
{-@ measure len @-}

{-@
data Eg [egLen] = Eg String @-}
data Eg         = Eg String

{-@
egLen :: Eg -> Int @-}
egLen (Eg xs) = len xs
{-@ measure egLen @-}
