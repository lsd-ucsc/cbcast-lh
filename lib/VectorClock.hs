
-- | Vector clocks implemented simply.
module VectorClock where

import Redefined




-- * Datatypes

-- | A clock value, which might be considered to be a count of messages.
{-@
type Clock = {c:Integer | 0 <= c} @-}
type Clock = Integer

-- | A vector clock maps an index (process identifier) to a Clock.
{-@
type VC = [Clock] @-}
type VC = [Clock]
{-@ type VCsized N = {v:VC | len v == N} @-}
{-@ type VCasV V = VCsized {len V} @-}

--- QQQ: everywhere an *asV type is defined, we call len, but perhaps we should
--- alias that here to vcSize
---
--- QQQ: similarly, everywhere we deal with proccount we specify Nat on the LH
--- side and Int on the haskell side; perhaps we should have a type alias here
---
--- QQQ: perhaps vcEmpty should be in terms of a Redefined.replicate




-- * Initialization

-- | The empty, initial, vc₀, vector clock.
{-@
vcEmpty :: n:Nat -> VCsized {n} @-}
vcEmpty :: Int -> VC
vcEmpty 0 = []
vcEmpty n = 0 : vcEmpty (n - 1)
{-@ reflect vcEmpty @-}




-- * Relations

{-@
vcLessEqual :: v:VC -> VCasV {v} -> Bool @-}
vcLessEqual :: VC -> VC -> Bool
vcLessEqual a b = listAnd (listZipWith vcLessEqualHelper a b)
{-@ reflect vcLessEqual @-}
vcLessEqualHelper :: Clock -> Clock -> Bool
vcLessEqualHelper a b = a <= b
{-@ reflect vcLessEqualHelper @-}

{-@
vcLess :: v:VC -> VCasV {v} -> Bool @-}
vcLess :: VC -> VC -> Bool
vcLess a b = vcLessEqual a b && a /= b
{-@ reflect vcLess @-}

{-@
vcConcurrent :: v:VC -> VCasV {v} -> Bool @-}
vcConcurrent :: VC -> VC -> Bool
vcConcurrent a b = not (vcLess a b) && not (vcLess b a)
{-@ reflect vcConcurrent @-}




-- * Operations

-- | Increment the ith offset into the VC (i=0 increments head).
{-@
vcTick :: v:VC -> {i:Nat | i < len v} -> VCasV {v} @-}
vcTick :: VC -> Int -> VC
vcTick (x:xs) 0 = (x + 1) : xs
vcTick (x:xs) i = x : vcTick xs (i - 1)
{-@ reflect vcTick @-}

-- | Return the elementwise max of two VCs.
{-@
vcCombine :: v:VC -> VCasV {v} -> VCasV {v} @-}
vcCombine :: VC -> VC -> VC
vcCombine = listZipWith ordMax
{-@ reflect vcCombine @-}
