module Crash where

{-@ LIQUID "--ple-local" @-}
{-@ LIQUID "--exact-data" @-}
import Language.Haskell.Liquid.ProofCombinators

{-@ reflect sameKeys @-}
sameKeys :: Eq a => [(a,b)] -> [(a,c)] -> Bool
sameKeys ((x,_):xs) ((y,_):ys) = x == y && sameKeys xs ys
sameKeys [] [] = True
sameKeys _ _ = False

-- | This is a reflected version of "impossible"
{-@ inline nope @-}
{-@ nope :: {_:_ | false } -> _ @-}
nope :: String -> Bool
nope _ = False

-- | This is a reflected function which requires PLE to pass.
{-@ reflect pairwiseValsEqual @-}
{-@ ple pairwiseValsEqual @-}
{-@ pairwiseValsEqual :: xs:[(a,b)] -> {ys:[(a,b)] | sameKeys xs ys} -> Bool @-}
pairwiseValsEqual :: Eq b => [(a,b)] -> [(a,b)] -> Bool
pairwiseValsEqual [] [] = True
pairwiseValsEqual [] _  = nope "same keys"
pairwiseValsEqual _  [] = nope "same keys"
pairwiseValsEqual ((_,x):xs) ((_,y):ys) = x == y && pairwiseValsEqual xs ys

{-@ ignore crash @-} -- FIXME: stop ignoring this function to cause a crash
{-@ ple crash @-}
{-@ crash :: xs:_ -> {ys:_ | pairwiseValsEqual xs ys} -> { sameKeys xs ys } @-}
crash :: [(Char,Int)] -> [(Char,Int)] -> Proof
crash [] [] = trivial
crash [] _  = unreachable
crash _  [] = unreachable
crash (_:_) (_:_) = trivial
