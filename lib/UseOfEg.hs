module UseOfEg where

import Eg

{-@ measure twoListSize @-}
twoListSize :: ([a], [b]) -> Int
twoListSize (as, bs) = listSize as + listSize bs


