module Redefined.Vec where

-- * Agda things reimplemented

-- | A list of fixed size.
{-@ type Vec a V = {v:[a] | len v == V} @-}
type Vec a = [a]

