module Verification where

-- | Reify the @len@ measure defined in the @liquid-base@ specification into
-- code and back into specifications.
{-@ measure listLength @-}
{-@
listLength :: x:[a] -> {y:Nat | len x == y} @-}
listLength :: [a] -> Int
listLength [] = 0
listLength (_x:xs) = 1 + listLength xs

first :: (a -> b) -> (a, z) -> (b, z)
first f (a, z) = (f a, z)

second :: (y -> z) -> (a, y) -> (a, z)
second f (a, y) = (a, f y)

{-@
fmapMaybe :: f:_ -> m:_ -> {m':_ |
    (isJust m <=> isJust m') &&
    (isJust m => f (fromJust m) == fromJust m')
    } @-}
fmapMaybe :: (a -> b) -> Maybe a -> Maybe b
fmapMaybe _ Nothing = Nothing
fmapMaybe f (Just a) = Just (f a)
