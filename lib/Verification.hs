module Verification where

-- | Reify the @len@ measure defined in the @liquid-base@ specification into
-- code and back into specifications.
{-@ measure listLength @-}
{-@
listLength :: x:[a] -> {y:Nat | len x == y} @-}
listLength :: [a] -> Int
listLength [] = 0
listLength (_x:xs) = 1 + listLength xs
