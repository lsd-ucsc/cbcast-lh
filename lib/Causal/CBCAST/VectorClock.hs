-- | Implementation of vector clocks as a list of integers.
--
-- To follow the proof, read this file until the operations at index K are
-- defined (around line 80), then proceed to Message.hs, and finally
-- Safety.hs.
module Causal.CBCAST.VectorClock where

import Redefined


-- * Types

-- | Specs are parameterized over uninterpreted @procCount@, for which no value
-- is given here.
{-@ measure procCount :: Nat @-}
{-@ type ProcCount = {s:Nat | s == procCount} @-}

-- | Clock values are an unbound-integer natural.
{-@
type Clock = {c:Integer | 0 <= c} @-}
type Clock = Integer

-- | PID is an index into a vector clock.
{-@
type PID = Fin {procCount} @-}
type PID = Fin

-- | A vector clock is a list of clock values of some uninterpreted length.
{-@
data VC [vcSize] = VC (Vec Clock {procCount}) @-}
data VC = VC [Clock]
    deriving (Eq, Show)

{-@ measure vcSize @-}
{-@
vcSize :: VC -> ProcCount @-}
vcSize :: VC -> Int
vcSize (VC []) = 0
vcSize (VC xs@(_:_)) = listLength xs


-- * Operations at index K

-- NOTE: These "at index K" operations are used for the safety proof. We take
-- `foldl` as part of our TCB to define operations over all K using these.

-- | Read an index in a vector clock.
--
-- >>> VC [9,8,7] `vcReadK` 0
-- 9
-- >>> VC [9,8,7] `vcReadK` 1
-- 8
-- >>> VC [9,8,7] `vcReadK` 2
-- 7
--
{-@ reflect vcReadK @-}
{-@
vcReadK :: VC -> PID -> Clock @-}
vcReadK :: VC -> PID -> Clock
vcReadK (VC xs) k = listIndex xs k

-- | Infix alias for 'vcReadK' with high precedence.
{-@ reflect ! @-}
{-@
(!) :: VC -> PID -> Clock @-}
(!) :: VC -> PID -> Clock
vc ! p = vcReadK vc p
infixl 9 !

-- | Compare less-equal at a single index the vector clocks.
{-@ reflect vcLessEqualK @-}
{-@
vcLessEqualK :: VC -> VC -> PID -> Bool @-}
vcLessEqualK :: VC -> VC -> PID -> Bool
vcLessEqualK a b k = a ! k <= b ! k

-- | Compare less-equal at a single index the vector clocks. Vector clock less
-- allows for equality at some indexes, but not all indexes, so this
-- implementation must check that the clocks aren't equal.
{-@ reflect vcLessK @-}
{-@
vcLessK :: VC -> VC -> PID -> Bool @-}
vcLessK :: VC -> VC -> PID -> Bool
vcLessK a b k = vcLessEqualK a b k && a /= b

-- The rest of this file is not important for reading the proof.


-- * Operations over all K

{-@ reflect iter @-}
{-@
iter :: n:Nat -> (Fin {n} -> Bool) -> Bool @-}
iter :: Int -> (Fin -> Bool) -> Bool
iter n f = listFoldr boolAnd True (listMap f (fin n))

-- | Compare two vector clocks with elementwise less-equal.
--
-- >>> vcLessEqual (VC []) (VC [])
-- True
-- >>> vcLessEqual (VC [0,0]) (VC [0,0])
-- True
--
-- >>> vcLessEqual (VC [0,1]) (VC [0,2])
-- True
-- >>> vcLessEqual (VC [2,1]) (VC [1,2])
-- False
--
{-@ reflect vcLessEqual @-}
{-@
vcLessEqual :: VC -> VC -> Bool @-}
vcLessEqual :: VC -> VC -> Bool
vcLessEqual a b = vcSize a `iter` vcLessEqualK a b

-- | Compare two vector clocks. Are they ordered and distinct?
--
-- >>> vcLess (VC []) (VC [])
-- False
-- >>> vcLess (VC [0,0]) (VC [0,0])
-- False
--
-- >>> vcLess (VC [0,1]) (VC [0,2])
-- True
-- >>> vcLess (VC [2,1]) (VC [1,2])
-- False
--
{-@ reflect vcLess @-}
{-@
vcLess :: VC -> VC -> Bool @-}
vcLess :: VC -> VC -> Bool
vcLess (VC []) (VC []) = False
vcLess a b = vcSize a `iter` vcLessK a b


-- * Additional vector clock functions

-- | Compare two vector clocks. Are they concurrent?
--
-- >>> vcIndependent (VC []) (VC [])
-- True
-- >>> vcIndependent (VC [0,0]) (VC [0,0])
-- True
--
-- >>> vcIndependent (VC [0,1]) (VC [0,2])
-- False
-- >>> vcIndependent (VC [2,1]) (VC [1,2])
-- True
--
{-@ reflect vcIndependent @-}
{-@
vcIndependent :: VC -> VC -> Bool @-}
vcIndependent :: VC -> VC -> Bool
vcIndependent a b = not (vcLess a b) && not (vcLess b a)

{-@ reflect vcNew @-}
{-@
vcNew :: ProcCount -> VC @-}
vcNew :: Int -> VC
vcNew size = VC (listReplicate size 0)

-- | Increment the index in a vector clock.
--
-- >>> vcTick 0 (VC [9,8,7])
-- VC [10,8,7]
-- >>> vcTick 1 (VC [9,8,7])
-- VC [9,9,7]
-- >>> vcTick 2 (VC [9,8,7])
-- VC [9,8,8]
--
-- >>> vcTick (-1) (VC [9,8,7])
-- ...Exception...
-- ...
-- >>> vcTick 3 (VC [9,8,7])
-- ...Exception...
-- ...
--
{-@ reflect vcTick @-}
{-@
vcTick :: PID -> VC -> VC @-}
vcTick :: PID -> VC -> VC
vcTick p (VC xs) = VC $ vcTickImpl p xs
{-@ reflect vcTickImpl @-}
{-@
vcTickImpl :: i:Nat -> {xs:[Clock] | i < len xs} -> {ys:[Clock] | len xs == len ys} @-}
vcTickImpl :: Int -> [Clock] -> [Clock]
vcTickImpl p (c:cs)
    | p == 0    = (c+1):cs
    | otherwise = c:vcTickImpl (p-1) cs

-- | Combine two vector clocks with elementwise max.
--
-- >>> vcCombine (VC []) (VC [])
-- VC []
-- >>> vcCombine (VC [0,0]) (VC [0,0])
-- VC [0,0]
--
-- >>> vcCombine (VC [0,1]) (VC [0,2])
-- VC [0,2]
-- >>> vcCombine (VC [2,1]) (VC [1,2])
-- VC [2,2]
--
{-@ reflect vcCombine @-}
{-@
vcCombine :: VC -> VC -> VC @-}
vcCombine :: VC -> VC -> VC
vcCombine (VC xs) (VC ys) = VC $ vcCombineImpl xs ys
{-@ reflect vcCombineImpl @-}
{-@
vcCombineImpl :: xs:[Clock] -> {ys:[Clock] | len xs == len ys} -> {zs:[Clock] | len xs == len zs && len ys == len zs} @-}
vcCombineImpl :: [Clock] -> [Clock] -> [Clock]
vcCombineImpl (x:xs) (y:ys) = (if x < y then y else x) : vcCombineImpl xs ys
vcCombineImpl [] [] = []
