-- |
--
-- These are definitions redefined from elsewhere for use with LiquidHaskell.
module Redefined where

-- $setup
-- >>> :set -XFlexibleInstances
-- >>> instance Show (a -> b) where show _ = "(a -> b)"

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
