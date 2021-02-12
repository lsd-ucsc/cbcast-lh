-- |
--
-- These are definitions redefined from elsewhere for use with LiquidHaskell.
module Redefined where

-- $setup
-- >>> :set -XFlexibleInstances
-- >>> instance Show (a -> b) where show _ = "(a -> b)"
-- >>> import Data.List

-- | Reify the @len@ measure defined in the @liquid-base@ specification into
-- code and back into specifications.
--
-- prop> length xs == listLength xs
{-@
listLength :: xs:_ -> {n:Nat | n == len xs } @-}
listLength :: [a] -> Int
listLength [] = 0
listLength (_x:xs) = 1 + listLength xs
{-@ measure listLength @-}

-- | Implementation of 'enumFromTo' lifted to specifications. Probably same as
-- 'Prelude'. Has extra preconditions and postconditions.
--
-- >>> listEnumFromTo 0 2
-- [0,1,2]
-- >>> listEnumFromTo 0 0
-- [0]
--
-- prop> enumFromTo x y == listEnumFromTo x y
{-@ reflect listEnumFromTo @-}
{-@ listEnumFromTo :: a:Int -> {b:Int | a <= b} -> [{n:Int | a <= n && n <= b}] / [b - a] @-}
listEnumFromTo :: Int -> Int -> [Int]
listEnumFromTo a b
    | b <  a = impossibleConst [] "precondition a less-eq b"
    | a == b = [a]
    | otherwise = a:listEnumFromTo (a+1) b

-- | Implementation of 'listZip' lifted to specifications. Probably same as
-- 'Prelude'. Has extra preconditions and postconditions.
--
-- >>> listZip "foo" "bar"
-- [('f','b'),('o','a'),('o','r')]
--
-- prop> let (xs,ys) = splitAt (length input `div` 2) input in zip xs ys == listZip xs ys
{-@ reflect listZip @-}
{-@ listZip :: xs:[a] -> {ys:[b] | len xs == len ys} -> {zs:[(a, b)] | len xs == len zs && len ys == len zs} @-}
listZip :: [a] -> [b] -> [(a, b)]
listZip (x:xs) (y:ys) = (x,y):listZip xs ys
listZip [] [] = []
listZip _ _ = impossibleConst [] "lists have same length"

-- | Implementation of 'fmap' over 'Maybe' lifted to specifications.
--
-- prop> fmap f m == maybeMap f m
maybeMap :: (a -> b) -> Maybe a -> Maybe b
maybeMap _ Nothing= Nothing
maybeMap f (Just a) = Just (f a)
{-@ reflect maybeMap @-}

-- | Implementation of 'break' lifted to specifications. Copied from 'Prelude',
-- but with changes to naming for readability.
--
-- >>> listBreak (> 'm') "hello world"
-- ("hell","o world")
--
-- Test whether this returns the same values as that of the 'Prelude'. It
-- should, since it's copied from there.
--
-- prop> break p xs == listBreak p xs
{-@
listBreak :: p:_ -> xs:_ -> ([{y:a | not (p y)}], {zs:_ | zs /= [] => p (head zs)})<{\ys zs -> listLength xs == listLength ys + listLength zs}> @-}
listBreak :: (a -> Bool) -> [a] -> ([a], [a])
listBreak _ [] = ([], [])
listBreak exclude (x:xs)
    | exclude x = ([], x:xs)
    | otherwise = let (incl,excl) = listBreak exclude xs in (x:incl,excl)
{-@ reflect listBreak @-}

-- | Implementation of '++' lifted to specifications. Copied from 'Prelude'.
--
-- prop> xs ++ ys == xs `listAppend` ys
{-@
listAppend :: xs:_ -> ys:_ -> {zs:_ | listLength xs + listLength ys == listLength zs} @-}
listAppend :: [a] -> [a] -> [a]
listAppend []     ys = ys
listAppend (x:xs) ys = x : xs `listAppend` ys
{-@ reflect listAppend @-}

-- | Implementation of 'reverse' lifted to specifications. Copied from
-- 'Prelude'.
--
-- prop> reverse xs == listReverse xs
{-@
listReverse :: xs:_ -> {ys:_ | listLength xs == listLength ys} @-}
listReverse :: [a] -> [a]
listReverse orig = listReverseImpl orig []
{-@ inline listReverse @-}

{-@
listReverseImpl :: xs:_ -> ys:_ -> {zs:_ | listLength xs + listLength ys == listLength zs} @-}
listReverseImpl :: [a] -> [a] -> [a]
listReverseImpl []     done = done
listReverseImpl (x:xs) done = listReverseImpl xs (x:done)
{-@ reflect listReverseImpl @-}

-- | Similar to @base:Data.List.elemIndex@ or
-- @containers:Data.Sequence.elemeIndexL@, "elemIndexL finds the leftmost index
-- of the specified element, if it is present, and otherwise Nothing," but is
-- implemented more simply.
--
-- prop> elemIndex a xs == listElemIndex a xs
{-@
listElemIndex :: x:_ -> xs:_ -> {m:_ | listElem x xs => isJust m} @-}
listElemIndex :: Eq a => a -> [a] -> Maybe Int
listElemIndex a xs = listElemIndexImpl a xs 0
{-@ inline listElemIndex @-}

{-@
listElemIndexImpl :: x:_ -> xs:_ -> _ -> {m:_ | listElem x xs => isJust m} @-}
listElemIndexImpl :: Eq a => a -> [a] -> Int -> Maybe Int
listElemIndexImpl _ [] _ = Nothing
listElemIndexImpl a (x:xs) idx
    | a == x = Just idx
    | otherwise = listElemIndexImpl a xs (idx + 1)
{-@ reflect listElemIndexImpl @-}
{-@ ple listElemIndexImpl @-}

-- | Implementation of 'elem' lifted to specifications. Copied from 'Prelude'.
--
-- prop> elem a xs == listElem a xs
listElem :: Eq a => a -> [a] -> Bool
listElem _ []     = False
listElem x (y:ys) = x==y || listElem x ys
{-@ reflect listElem @-}

-- | Implementation of 'impossible' lifted to specifications. similar to the
-- one in 'Language.Haskell.Liquid.ProofCombinators'.
{-@ inline impossibleConst @-}
{-@ impossibleConst :: a -> {v:b | false } -> a @-}
impossibleConst :: a -> b -> a
impossibleConst a _ = a
