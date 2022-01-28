module Redefined.Ord where

-- | Implementation of 'max' lifted to specifications.
--
-- prop> max a b == ordMax a b
{-@ reflect ordMax @-}
ordMax :: Ord a => a -> a -> a
ordMax x y = if x < y then y else x
