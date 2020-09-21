{-# LANGUAGE QuasiQuotes #-}
module Help where

import LiquidHaskell (lq)

{-@
data Eg [egLen] = Eg String @-}
data Eg         = Eg String

[lq|
egLen :: Eg -> Int |]
egLen (Eg s) = length s
[lq| measure egLen |]

-- works, but :(
--
-- [lq|
-- egLen :: Eg -> Int |]
-- egLen (Eg xs) = len xs
-- [lq| measure egLen |]
-- 
-- [lq|
-- len :: [a] -> Int |]
-- len [] = 0
-- len (_x:xs) = 1 + len xs
-- [lq| measure len |]
