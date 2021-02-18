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

-- | Implementation of 'and' lifted to specifications. Probably same as
-- 'Prelude'.
--
-- prop> and xs == listAnd xs
{-@ reflect listAnd @-} -- FIXME: this causes a crash when it's a measure?
listAnd :: [Bool] -> Bool
listAnd [] = True
listAnd (b:bs) = b && listAnd bs

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
