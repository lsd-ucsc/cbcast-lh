module Eg where

{-@ measure listSize @-}
listSize :: [a] -> Int
listSize [] = 0
listSize (_x:xs) = 1 + listSize xs
