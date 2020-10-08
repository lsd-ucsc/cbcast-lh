module Verification where

-- | Reify the @len@ measure defined in the @liquid-base@ specification into
-- code and back into specifications.
{-@
listLength :: xs:_ -> {n:Nat | n == len xs } @-}
listLength :: [a] -> Int
listLength [] = 0
listLength (_x:xs) = 1 + listLength xs
{-@ measure listLength @-}

first :: (a -> b) -> (a, z) -> (b, z)
first f (a, z) = (f a, z)

second :: (y -> z) -> (a, y) -> (a, z)
second f (a, y) = (a, f y)

fmapMaybe :: (a -> b) -> Maybe a -> Maybe b
fmapMaybe _ Nothing = Nothing
fmapMaybe f (Just a) = Just (f a)
