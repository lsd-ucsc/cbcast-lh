{-@ LIQUID "--reflection" @-} 
{-@ LIQUID "--ple" @-}
module Causal.CBCAST.ForAll where

import Redefined

import Language.Haskell.Liquid.ProofCombinators
import Prelude hiding (all, elem)

{-@ reflect all @-}
all :: (a -> Bool) -> [a] -> Bool
all _p []     = True
all  p (x:xs) = p x && all p xs

{-@ reflect upTo @-}
{-@ upTo :: n:Nat -> [Fin n] @-}
upTo :: Int -> [Int]
upTo 0 = []
upTo n = n-1 : upTo (n-1)

{-@ reflect elem @-}
elem :: Int -> [Int] -> Bool
elem y []     = False
elem y (x:xs) = y == x || elem y xs

{-@ upToInFin :: n:Nat -> k:(Fin n) -> {_:Proof | elem k (upTo n)} @-}
upToInFin :: Int -> Int -> Proof
upToInFin 0 k = ()
upToInFin n k =
  if k == n-1
  then ()
  else upTo n `seq` upToInFin (n-1) k

{-@ allFin :: n:Nat -> k:(Fin n) -> p:(Int -> Bool) -> {_:Proof | all p (upTo n) = True} -> {p k == True} @-}
allFin :: Int -> Int -> (Int -> Bool) -> Proof -> Proof
allFin 0 _k _p _pf = ()
allFin n  k  p  pf =
  if k == n-1
  then ()
  else allFin (n-1) k p pf
