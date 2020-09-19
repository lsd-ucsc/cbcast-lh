{-# LANGUAGE QuasiQuotes #-}
module Causal.VectorclockConcrete where

--import Language.Haskell.Liquid.ProofCombinators (Proof, trivial)
import LiquidHaskell (lq)

import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Map.Merge.Lazy as Merge

import Data.List (intercalate)
import Data.UUID (UUID)

-- $setup
-- >>> import qualified Data.UUID as UUID
-- >>> let fives = UUID.fromWords 5 5 5 5
-- >>> let sixes = UUID.fromWords 6 6 6 6
-- >>> let sevens = UUID.fromWords 7 7 7 7
-- >>> let eights = UUID.fromWords 8 8 8 8

-- * Common

[lq|
type Natural = {i:Integer | 0 <= i} |]

-- * Clocks

[lq|
newtype Clock = Clock {cRaw :: Natural} |]
newtype Clock = Clock {cRaw :: Natural}
    deriving (Eq, Ord)
[lq|
cStart :: Clock |]
cStart = Clock 0
[lq|
cInc :: Clock -> Clock |]
cInc (Clock c) = Clock (c + 1)

-- * Vector clocks

[lq|
newtype Vectorclock = Vectorclock {vcRaw :: Map UUID Clock} |]
newtype Vectorclock = Vectorclock {vcRaw :: Map UUID Clock}
    deriving Eq
-- |
-- >>> vcNew
-- empty-vc
[lq|
vcNew :: Vectorclock |]
vcNew = Vectorclock Map.empty
-- |
-- >>> vcTick fives vcNew
-- 00000005-0000-0005-0000-000500000005:t1
-- >>> vcTick fives . Vectorclock $ Map.fromList [(eights, Clock 0), (fives, Clock 0)]
-- 00000005-0000-0005-0000-000500000005:t1
-- 00000008-0000-0008-0000-000800000008:t0
-- >>> vcTick fives . Vectorclock $ Map.fromList [(eights, Clock 3), (fives, Clock 4)]
-- 00000005-0000-0005-0000-000500000005:t5
-- 00000008-0000-0008-0000-000800000008:t3
[lq|
vcTick :: UUID -> Vectorclock -> Vectorclock |]
vcTick pid (Vectorclock vc) = Vectorclock
    (Map.alter (pure . cInc . maybe cStart id) pid vc)
[lq|
vcCombine :: Vectorclock -> Vectorclock -> Vectorclock |]
vcCombine (Vectorclock a) (Vectorclock b) = Vectorclock
    (Map.unionWith max a b)
[lq|
vcLessEqual :: Vectorclock -> Vectorclock -> Bool |]
vcLessEqual (Vectorclock a) (Vectorclock b)
    = and . Map.elems $ Merge.merge
        (Merge.mapMissing $ const (<= cStart))
      {-(Merge.mapMissing $ const (cStart <=))-} Merge.dropMissing
        (Merge.zipWithMatched $ const (<=))
        a b
[lq|
vcLess :: Vectorclock -> Vectorclock -> Bool |]
vcLess a b = vcLessEqual a b && a /= b
[lq|
vcIndependent :: Vectorclock -> Vectorclock -> Bool |]
vcIndependent a b = not (vcLess a b) && not (vcLess b a)

-- * Show instances for tests

instance Show Clock where
    show (Clock c) = 't' : show c

instance Show Vectorclock where
    show (Vectorclock vc)
        | Map.null vc = "empty-vc"
        | otherwise
            = intercalate "\n"
            . fmap (\(k, v) -> show k ++ ':' : show v)
            $ Map.toAscList vc
