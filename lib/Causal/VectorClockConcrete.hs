{-|
Description: Vector clocks implemented with maps keyed on UUIDs.
-}
{-# LANGUAGE QuasiQuotes #-}
module Causal.VectorClockConcrete
( VectorClock()
, vcNew
, vcTick
, vcCombine
, vcLessEqual
, vcLess
, vcIndependent
) where

import qualified Data.Map as Map
import qualified Data.Map.Merge.Lazy as Merge

import Data.List (intercalate)
import Data.UUID (UUID)

import LiquidHaskell (lq)

-- $setup
-- >>> import qualified Data.UUID as UUID
-- >>> let cafe = UUID.fromWords 0xcafe 0xcafe 0xcafe 0xcafe
-- >>> let beef = UUID.fromWords 0xbeef 0xbeef 0xbeef 0xbeef
-- >>> :set -XStandaloneDeriving -XGeneralizedNewtypeDeriving
-- >>> deriving instance Num Clock
-- >>> let vc = VectorClock . Map.fromList

-- * Clocks

newtype Clock = Clock Integer
    deriving (Eq, Ord)
cStart :: Clock
cStart = Clock 0
cInc :: Clock -> Clock
cInc (Clock c) = Clock (c + 1)

-- * Vector clocks

[lq|
newtype VectorClock = VectorClock (Map.Map UUID Clock) |]
newtype VectorClock = VectorClock (Map.Map UUID Clock)
    deriving Eq
-- |
-- >>> vcNew
-- empty-vc
vcNew :: VectorClock
vcNew = VectorClock Map.empty
-- |
-- >>> vcTick cafe vcNew
-- 0000cafe-0000-cafe-0000-cafe0000cafe:t1
-- >>> vcTick cafe $ vc [(beef, 0), (cafe, 0)]
-- 0000cafe-0000-cafe-0000-cafe0000cafe:t1
-- 0000beef-0000-beef-0000-beef0000beef:t0
-- >>> vcTick cafe $ vc [(beef, 3), (cafe, 4)]
-- 0000cafe-0000-cafe-0000-cafe0000cafe:t5
-- 0000beef-0000-beef-0000-beef0000beef:t3
vcTick :: UUID -> VectorClock -> VectorClock
vcTick pid (VectorClock vc) = VectorClock
    (Map.alter (pure . cInc . maybe cStart id) pid vc)
-- |
-- >>> let a = vc [(beef, 9)]
-- >>> let b = vc [(beef, 3), (cafe, 4)]
-- >>> vcCombine vcNew vcNew
-- empty-vc
-- >>> vcCombine a vcNew
-- 0000beef-0000-beef-0000-beef0000beef:t9
-- >>> vcCombine vcNew b
-- 0000cafe-0000-cafe-0000-cafe0000cafe:t4
-- 0000beef-0000-beef-0000-beef0000beef:t3
-- >>> vcCombine a b
-- 0000cafe-0000-cafe-0000-cafe0000cafe:t4
-- 0000beef-0000-beef-0000-beef0000beef:t9
vcCombine :: VectorClock -> VectorClock -> VectorClock
vcCombine (VectorClock a) (VectorClock b) = VectorClock
    (Map.unionWith max a b)
-- |
-- >>> vcLessEqual vcNew vcNew
-- True
--
-- >>> vcLessEqual (vc [(beef, 0), (cafe, 0)]) (vc [(beef, 0), (cafe, 0)])
-- True
-- >>> vcLessEqual (vc [(beef, 0), (cafe, 0)]) (vc [(beef, 1), (cafe, 1)])
-- True
-- >>> vcLessEqual (vc [(beef, 1), (cafe, 1)]) (vc [(beef, 1), (cafe, 1)])
-- True
-- >>> vcLessEqual (vc [(beef, 1), (cafe, 2)]) (vc [(beef, 1), (cafe, 1)])
-- False
--
-- >>> vcLessEqual (vc [(beef, 9)]) (vc [(beef, 3), (cafe, 4)])
-- False
-- >>> vcLessEqual (vc [(beef, 3), (cafe, 4)]) (vc [(beef, 9)])
-- False
-- >>> vcLessEqual (vc [(beef, 1)]) (vc [(beef, 3), (cafe, 4)])
-- True
-- >>> vcLessEqual (vc [(beef, 3), (cafe, 0)]) (vc [(beef, 9)])
-- True
vcLessEqual :: VectorClock -> VectorClock -> Bool
vcLessEqual (VectorClock a) (VectorClock b)
    = and . Map.elems $ Merge.merge
        (Merge.mapMissing $ const (<= cStart))
      {-(Merge.mapMissing $ const (cStart <=))-} Merge.dropMissing
        (Merge.zipWithMatched $ const (<=))
        a b
-- |
vcLess :: VectorClock -> VectorClock -> Bool
vcLess a b = vcLessEqual a b && a /= b
-- |
-- >>> vcIndependent vcNew vcNew
-- True
vcIndependent :: VectorClock -> VectorClock -> Bool
vcIndependent a b = not (vcLess a b) && not (vcLess b a)

-- * Show instances for tests

instance Show Clock where
    show (Clock c) = 't' : show c

instance Show VectorClock where
    show (VectorClock vc)
        | Map.null vc = "empty-vc"
        | otherwise
            = intercalate "\n"
            . fmap (\(k, v) -> show k ++ ':' : show v)
            $ Map.toDescList vc
