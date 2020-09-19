{-# LANGUAGE QuasiQuotes #-}
{-|
Description: VectorClocks implemented with maps keyed on UUIDs.
-}
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
-- >>> let cafe = UUID.fromWords 0xcafe 0xcafe 0xcafe 0xcafe
-- >>> let beef = UUID.fromWords 0xbeef 0xbeef 0xbeef 0xbeef
-- >>> :set -XStandaloneDeriving -XGeneralizedNewtypeDeriving
-- >>> deriving instance Num Clock
-- >>> let vc = Vectorclock . Map.fromList

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
-- >>> vcTick cafe vcNew
-- 0000cafe-0000-cafe-0000-cafe0000cafe:t1
-- >>> vcTick cafe $ vc [(beef, 0), (cafe, 0)]
-- 0000cafe-0000-cafe-0000-cafe0000cafe:t1
-- 0000beef-0000-beef-0000-beef0000beef:t0
-- >>> vcTick cafe $ vc [(beef, 3), (cafe, 4)]
-- 0000cafe-0000-cafe-0000-cafe0000cafe:t5
-- 0000beef-0000-beef-0000-beef0000beef:t3
[lq|
vcTick :: UUID -> Vectorclock -> Vectorclock |]
vcTick pid (Vectorclock vc) = Vectorclock
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
[lq|
vcCombine :: Vectorclock -> Vectorclock -> Vectorclock |]
vcCombine (Vectorclock a) (Vectorclock b) = Vectorclock
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
-- |
-- >>> vcIndependent vcNew vcNew
-- True
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
            $ Map.toDescList vc
