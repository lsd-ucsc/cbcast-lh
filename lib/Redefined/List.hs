module Redefined.List where

import Redefined.Bool
import Redefined.Fin ()

-- $setup
-- >>> :set -XFlexibleInstances
-- >>> instance Show (a -> b) where show _ = "(a -> b)"
-- >>> import Data.List

-- | Reify the @len@ measure defined in the @liquid-base@ specification into
-- code and back into specifications.
--
-- prop> length xs == listLength xs
{-@ measure listLength @-}
{-@ listLength :: xs:_ -> {v:Nat | v == len xs } @-}
listLength :: [a] -> Int
listLength [] = 0
listLength (_x:xs) = 1 + listLength xs

-- | Implementation of 'replicate' lifted to specifications. Probably same as
-- that of 'Prelude'.
--
-- prop> replicate n x == listReplicate n x
{-@ reflect listReplicate @-}
{-@ listReplicate :: n:Nat -> item:a -> {xs:[{x:a | x == item}] | n == listLength xs} @-}
listReplicate :: Int -> a -> [a]
listReplicate n x
    | n <= 0    = []
    | otherwise = x:listReplicate (n-1) x

-- | Implementation of 'map' lifted to specifications. Probably same as
-- 'Prelude'.
--
-- prop> map f xs == listMap f xs
{-@ reflect listMap @-}
listMap :: (a -> b) -> [a] -> [b]
listMap f (x:xs) = f x:listMap f xs
listMap _ [] = []

-- | Implementation of 'foldr' lifted to specifications. Probably same as
-- 'Prelude'.
--
-- prop> foldr f acc xs == listFoldr f acc xs
{-@ reflect listFoldr @-}
listFoldr :: (a -> b -> b) -> b -> [a] -> b
listFoldr f acc (x:xs) = f x (listFoldr f acc xs)
listFoldr _ acc [] = acc

-- | Implementation of 'and' lifted to specifications. Probably same as
-- 'Prelude'.
--
-- prop> and xs == listAnd xs
{-@ reflect listAnd @-} -- FIXME: this causes a crash when it's a measure?
listAnd :: [Bool] -> Bool
listAnd = listFoldr boolAnd True

-- | Implementation of 'or' lifted to specifications. Probably same as
-- 'Prelude'.
--
-- prop> or xs == listOr xs
{-@ reflect listOr @-} -- FIXME: this causes a crash when it's a measure?
listOr :: [Bool] -> Bool
listOr = listFoldr boolOr False

-- | Implementation of 'reverse' lifted to specifications. Copied from
-- 'Prelude'.
--
-- prop> reverse xs == listReverse xs
{-@ inline listReverse @-}
{-@ listReverse :: xs:_ -> {ys:_ | listLength xs == listLength ys} @-}
listReverse :: [a] -> [a]
listReverse orig = listReverseImpl orig []

{-@ reflect listReverseImpl @-}
{-@ listReverseImpl :: xs:_ -> ys:_ -> {zs:_ | listLength xs + listLength ys == listLength zs} @-}
listReverseImpl :: [a] -> [a] -> [a]
listReverseImpl []     done = done
listReverseImpl (x:xs) done = listReverseImpl xs (x:done)

-- | Similar to @base:Data.List.elemIndex@ or
-- @containers:Data.Sequence.elemeIndexL@, "elemIndexL finds the leftmost index
-- of the specified element, if it is present, and otherwise Nothing," but is
-- implemented more simply.
--
-- prop> elemIndex a xs == listElemIndex a xs
{-@ inline listElemIndex @-}
{-@ listElemIndex :: x:_ -> xs:_ -> {m:_ | listElem x xs => isJust m} @-}
listElemIndex :: Eq a => a -> [a] -> Maybe Int
listElemIndex a xs = listElemIndexImpl a xs 0

{-@ reflect listElemIndexImpl @-}
{-@ listElemIndexImpl :: x:_ -> xs:_ -> _ -> {m:_ | listElem x xs => isJust m} @-}
{-@ ple listElemIndexImpl @-}
listElemIndexImpl :: Eq a => a -> [a] -> Int -> Maybe Int
listElemIndexImpl _ [] _ = Nothing
listElemIndexImpl a (x:xs) idx
    | a == x = Just idx
    | otherwise = listElemIndexImpl a xs (idx + 1)

-- | Implementation of 'elem' lifted to specifications. Copied from 'Prelude'.
--
-- prop> elem a xs == listElem a xs
{-@ reflect listElem @-}
listElem :: Eq a => a -> [a] -> Bool
listElem _ []     = False
listElem x (y:ys) = x==y || listElem x ys

-- | Implementation of 'init' combined with 'last' lifted to specifications.
--
-- prop> not (null xs) ==> (init xs, last xs) == listInitLast xs
{-@ reflect listInitLast @-}
{-@ listInitLast :: {xs:[a] | 0 < len xs} -> ([a], a) @-}
listInitLast :: [a] -> ([a], a)
listInitLast [x] = ([], x)
listInitLast (a:b:cs) = let (xs, x) = listInitLast (b:cs) in (a:xs, x)

-- | Lookup an element of a non-empty list given a valid index. This is called
-- "lookup" in agda and "!!" or "genericIndex" in haskell.
--
-- prop> 0 <= i && i < length xs ==> xs !! i == listIndex xs i
{-@ reflect listIndex @-}
{-@ listIndex :: xs:[a] -> Fin {len xs} -> a @-}
listIndex :: [a] -> Int -> a
listIndex (x:xs) i
    | i == 0    = x
    | otherwise = listIndex xs (i-1)

