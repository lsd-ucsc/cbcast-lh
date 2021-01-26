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

-- | Classless implementation of Arrow(first).
--
-- No idea why, but this property fails.
--
-- !prop> first f t == tupleFirst f t
tupleFirst :: (a -> b) -> (a, z) -> (b, z)
tupleFirst f (a, z) = (f a, z)
{-@ inline tupleFirst @-}

-- | Classless implementation of Arrow(second).
--
-- No idea why, but this property fails.
--
-- !prop> second f t == tupleSecond f t
tupleSecond :: (y -> z) -> (a, y) -> (a, z)
tupleSecond f (a, y) = (a, f y)
{-@ inline tupleSecond @-}

-- | Redefinition of 'Maybe' but for which we will lift functions into
-- specifications. Uses Rust's naming here just to make it very obviously a
-- distinct type, but this is isomorphic to 'Maybe'.
data Option t = None | Some t

-- | Reflected implementation of 'fmap' over 'Maybe'.
--
-- TODO: prop test to assert the isomorphism
optionMap :: (t -> u) -> Option t -> Option u
optionMap _ None = None
optionMap f (Some s) = Some (f s)
{-@ inline optionMap @-}

-- | Implementation of 'fmap' over 'Maybe' lifted to specifications.
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
listBreak :: p:_ -> xs:_ -> ([{x:a | not (p x)}], [a])<{\a b -> listLength xs == listLength a + listLength b}> @-}
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
listElemIndex :: Eq a => a -> [a] -> Maybe Int
listElemIndex a xs = listElemIndexImpl a xs 0
{-@ inline listElemIndex @-}

listElemIndexImpl :: Eq a => a -> [a] -> Int -> Maybe Int
listElemIndexImpl _ [] _ = Nothing
listElemIndexImpl a (x:xs) idx
    | a == x = Just idx
    | otherwise = listElemIndexImpl a xs (idx + 1)
{-@ reflect listElemIndexImpl @-}
