module Redefined.Proof where

-- * LiquidHaskell proof-combinators reimplemented

-- | Implementation of @impossible@ lifted to specifications. Similar to the
-- one in 'Language.Haskell.Liquid.ProofCombinators'.
--
{-# INLINE impossibleConst #-} -- GHC should eliminate uses of this
{-@ inline impossibleConst @-}
{-@ impossibleConst :: a -> {v:b | false } -> a @-}
impossibleConst :: a -> b -> a
impossibleConst a _ = a

-- | Implementation of @(?)@/@withProof@ lifted to specifications. Similar to
-- the one in 'Language.Haskell.Liquid.ProofCombinators'.
--
{-# INLINE proofConst #-} -- GHC should eliminate uses of this
{-@ inline proofConst @-}
proofConst :: a -> b -> a
proofConst x _ = x

