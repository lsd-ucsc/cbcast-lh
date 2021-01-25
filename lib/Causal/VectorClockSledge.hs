{-# LANGUAGE NamedFieldPuns #-}
module Causal.VectorClockSledge where

import Data.UUID (UUID)

-- $setup
-- >>> import qualified Data.List as List
-- >>> import qualified Data.UUID as UUID
-- >>> import qualified Test.QuickCheck as QC
-- >>> instance QC.Arbitrary UUID where arbitrary = UUID.fromWords <$> QC.arbitrary <*> QC.arbitrary <*> QC.arbitrary <*> QC.arbitrary
-- >>> instance QC.Arbitrary p => QC.Arbitrary (VCPoly p) where arbitrary = QC.oneof [return Nil, VC <$> QC.arbitrary <*> QC.arbitrary <*> QC.arbitrary]
-- >>> instance QC.Arbitrary VectorClock where arbitrary = VectorClock <$> QC.arbitrary
-- >>> let beef = UUID.fromWords 0xbeef 0xbeef 0xbeef 0xbeef
-- >>> let cafe = UUID.fromWords 0xcafe 0xcafe 0xcafe 0xcafe
-- >>> let face = UUID.fromWords 0xface 0xface 0xface 0xface
-- >>> beef < cafe && cafe < face
-- True
-- >>> (#) = vcTick; infixr 5 #


-- * Types

-- | Vector clock with polymorphic process-id and a refinement that guarantees
-- the clocks are valid, the PIDs in-order, and consequently the PIDs are
-- unique.
data VCPoly pid
    = Nil
    | VC
        { vcPid     :: pid
        , vcClock   :: RealClock
        , vcRest    :: VCPoly pid
        }
    deriving Eq
{-@
data VCPoly [vcpSize] _ where
      Nil :: _
    | VC :: pid:_ -> RealClock -> VCPoly {restPid:_ | pid < restPid} -> _
@-}
-- FIXME: bug in LH? The fields on this data structure do not have measures

-- | Concretely-typed vector clock carrying the refinement guarantees.
data VectorClock = VectorClock (VCPoly UUID)
    deriving Eq
{-@
data VectorClock [vcSize] @-}


-- * Logical predicates

-- |
--
-- >>> larger 1 2
-- 2
-- >>> larger 2 1
-- 2
larger :: Ord a => a -> a -> a
larger a b = if a > b then a else b
{-@ inline larger @-}

{-@
vcpSize :: _ -> Nat @-}
vcpSize :: VCPoly p -> Int
vcpSize Nil = 0
vcpSize VC{vcRest} = 1 + vcpSize vcRest
{-@ measure vcpSize @-}

{-@
vcSize :: _ -> Nat @-}
vcSize :: VectorClock -> Int
vcSize (VectorClock vc) = vcpSize vc
{-@ measure vcSize @-}

-- |
--
-- Base cases.
--
-- >>> vcHasPid vcNew beef -- nil
-- False
-- >>> vcHasPid (cafe # vcNew) cafe -- found
-- True
--
-- Recursive cases.
--
-- >>> vcHasPid (cafe # vcNew) beef -- search, nil
-- False
-- >>> vcHasPid (cafe # face # vcNew) face -- search, found
-- True
--
-- QuickCheck properties.
--
-- prop> not $ vcHasPid vcNew pid
-- prop>       vcHasPid (pid # vcNew) pid
vcHasPid :: VectorClock -> UUID -> Bool
vcHasPid (VectorClock vc) pid = vcHasPidImpl vc pid
{-@ inline vcHasPid @-}

vcHasPidImpl :: Eq p => VCPoly p -> p -> Bool
vcHasPidImpl Nil               _                  = {-nil   -} False
vcHasPidImpl VC{vcPid, vcRest} pid
                                   | vcPid == pid = {-found -} True
                                   | otherwise    = {-search-} vcHasPidImpl vcRest pid
{-@ reflect vcHasPidImpl @-}


-- * User API

-- |
--
-- >>> vcNew
-- empty-vc
vcNew :: VectorClock
vcNew = VectorClock Nil
{-@ inline vcNew @-}

-- |
--
-- These tests don't use vcTick to construct the vector clock because that's
-- what is under test.
--
-- Base cases.
--
-- >>> cafe `vcTick` (VectorClock $ Nil) -- nil
-- 0000cafe-0000-cafe-0000-cafe0000cafe:t1
-- >>> beef `vcTick` (VectorClock . VC cafe rcMin $ Nil) -- insert
-- 0000beef-0000-beef-0000-beef0000beef:t1
-- 0000cafe-0000-cafe-0000-cafe0000cafe:t1
-- >>> cafe `vcTick` (VectorClock . VC cafe rcMin $ Nil) -- update
-- 0000cafe-0000-cafe-0000-cafe0000cafe:t2
--
-- Recursive cases.
--
-- >>> face `vcTick` (VectorClock . VC cafe rcMin $ Nil) -- search, nil
-- 0000cafe-0000-cafe-0000-cafe0000cafe:t1
-- 0000face-0000-face-0000-face0000face:t1
--
-- Longer test.
--
-- >>> cafe `vcTick` (VectorClock . VC beef rcMin . VC cafe rcMin . VC face rcMin $ Nil)
-- 0000beef-0000-beef-0000-beef0000beef:t1
-- 0000cafe-0000-cafe-0000-cafe0000cafe:t2
-- 0000face-0000-face-0000-face0000face:t1
--
-- QuickCheck property showing that the result is the same regardless of the
-- order of ticks.
--
-- prop> vcTick a (vcTick b vcNew) == vcTick b (vcTick a vcNew)
--
-- QuickCheck property showing how the presence of a pid relates to vc size
-- after a tick.
--
-- prop> vcSize (vcTick pid v) == vcSize (vcTick pid (vcTick pid v))
-- prop> not (vcHasPid v pid) ==> vcSize v + 1 == vcSize (vcTick pid v)
vcTick :: UUID -> VectorClock -> VectorClock
vcTick pid (VectorClock vc) = VectorClock (vcTickImpl pid vc)
{-@ inline vcTick @-}

vcTickImpl :: Ord p => p -> VCPoly p -> VCPoly p
vcTickImpl pid vc = case vc of
    Nil                                     -> {-nil   -} new
    VC{vcPid,vcClock,vcRest}
                             | pid <  vcPid -> {-insert-} new{vcRest=vc{vcPid}} -- FIXME: LH requires that we prove vc has vcPid which is LT pid
                             | pid == vcPid -> {-update-} vc{vcClock=vcClock + 1}
                             | otherwise    -> {-search-} vc{vcRest=vcTickImpl pid vcRest}
  where
    new = VC pid rcMin Nil
{-@ reflect vcTickImpl @-}

-- |
--
-- Base cases.
--
-- >>> vcCombine vcNew (beef # vcNew) -- x-nil
-- 0000beef-0000-beef-0000-beef0000beef:t1
-- >>> vcCombine (beef # vcNew) vcNew -- y-nil
-- 0000beef-0000-beef-0000-beef0000beef:t1
--
-- Recursive cases.
--
-- >>> vcCombine (beef # vcNew) (cafe # vcNew) -- x-ahead, x-nil
-- 0000beef-0000-beef-0000-beef0000beef:t1
-- 0000cafe-0000-cafe-0000-cafe0000cafe:t1
-- >>> vcCombine (cafe # vcNew) (cafe # vcNew) -- compare, x-nil
-- 0000cafe-0000-cafe-0000-cafe0000cafe:t1
-- >>> vcCombine (cafe # cafe # vcNew) (cafe # vcNew) -- compare, x-nil (left is larger)
-- 0000cafe-0000-cafe-0000-cafe0000cafe:t2
-- >>> vcCombine (cafe # vcNew) (cafe # cafe # vcNew) -- compare, x-nil (right is larger)
-- 0000cafe-0000-cafe-0000-cafe0000cafe:t2
-- >>> vcCombine (face # vcNew) (cafe # vcNew) -- y-ahead, y-nil
-- 0000cafe-0000-cafe-0000-cafe0000cafe:t1
-- 0000face-0000-face-0000-face0000face:t1
--
-- QuickCheck property for commutativity.
--
-- prop> vcCombine a b == vcCombine b a
vcCombine :: VectorClock -> VectorClock -> VectorClock
vcCombine (VectorClock a) (VectorClock b) = VectorClock (vcCombineImpl a b)
{-@ inline vcCombine @-}

{-@
vcCombineImpl :: a:_ -> b:_ -> _ / [vcpSize a + vcpSize b] @-}
vcCombineImpl :: Ord p => VCPoly p -> VCPoly p -> VCPoly p
vcCombineImpl Nil                      y                                       = {-x-nil  -} y
vcCombineImpl x                        Nil                                     = {-y-nil  -} x
vcCombineImpl x@(VC xPid xClock xRest) y@(VC yPid yClock yRest)
                                                                | xPid <  yPid = {-x-ahead-} VC xPid  xClock                  (vcCombineImpl xRest         y{vcPid=yPid}) -- FIXME: LH requires that we prove y has yPid which is GT xPid
                                                                | xPid == yPid = {-combine-} VC xPid (xClock `larger` yClock) (vcCombineImpl xRest         yRest        )
                                                                | otherwise    = {-y-ahead-} VC yPid                  yClock  (vcCombineImpl x{vcPid=xPid} yRest        ) -- FIXME: LH requires that we prove x has xPid which is GT yPid
{-@ reflect vcCombineImpl @-}

-- |
--
-- Base cases.
--
-- >>> vcLessEqual vcNew vcNew -- nil-nil
-- True
--
-- Boring recursive cases.
--
-- >>> vcLessEqual (beef # vcNew) vcNew -- y-nil, nil-nil (always false because absent values are zero: 1 <= 0 is false)
-- False
-- >>> vcLessEqual (VectorClock . VC beef cMin $ Nil) vcNew -- y-nil, nil-nil (invalid data flips the result: 0 <= 0 is true)
-- True
-- >>> vcLessEqual vcNew (beef # vcNew) -- x-nil, nil-nil (always true because absent values are zero: 0 <= 1 is true)
-- True
-- >>> vcLessEqual vcNew (VectorClock . VC beef cMin $ Nil) -- x-nil, nil-nil (invalid data: 0 <= 0 is still true)
-- True
-- >>> vcLessEqual vcNew (VectorClock . VC beef (cMin-1) $ Nil) -- x-nil, nil-nil (invalid data flips the result: 0 <= -1 is false)
-- False
--
-- Recursive cases.
--
-- >>> vcLessEqual (beef # vcNew) (cafe # vcNew) -- x-ahead, x-nil
-- False
-- >>> vcLessEqual (beef # cafe # vcNew) (cafe # vcNew) -- x-ahead, compare, nil-nil
-- False
-- >>> vcLessEqual (cafe # vcNew) (cafe # vcNew) -- compare, nil-nil
-- True
-- >>> vcLessEqual (cafe # cafe # vcNew) (cafe # vcNew) -- compare, nil-nil (left is larger: 2 <= 1 is false)
-- False
-- >>> vcLessEqual (cafe # vcNew) (cafe # cafe # vcNew) -- compare, nil-nil (right is larger: 1 <= 2 is true)
-- True
-- >>> vcLessEqual (face # vcNew) (cafe # vcNew) -- y-ahead, y-nil
-- False
--
-- Longer test.
--
-- >>> vcLessEqual (beef # cafe # face # vcNew) (beef # cafe # face # vcNew)
-- True
-- >>> vcLessEqual (beef # cafe # face # vcNew) (beef # face # vcNew)
-- False
-- >>> vcLessEqual (beef # face # vcNew) (beef # cafe # face # vcNew)
-- True
vcLessEqual :: VectorClock -> VectorClock -> Bool
vcLessEqual (VectorClock a) (VectorClock b) = vcLessEqualImpl a b
{-@ inline vcLessEqual @-}

{-@
vcLessEqualImpl :: a:_ -> b:_ -> _ / [vcpSize a + vcpSize b] @-}
vcLessEqualImpl :: Ord p => VCPoly p -> VCPoly p -> Bool
vcLessEqualImpl Nil                      Nil                                     = {-nil-nil-} True
vcLessEqualImpl   (VC _    xClock xRest) Nil                                     = {-y-nil  -} xClock <= cMin   {-F-} && vcLessEqualImpl xRest Nil
vcLessEqualImpl Nil                        (VC _    yClock yRest)                = {-x-nil  -} cMin   <= yClock {-T-} && vcLessEqualImpl Nil   yRest
vcLessEqualImpl x@(VC xPid xClock xRest) y@(VC yPid yClock yRest)
                                                                  | xPid <  yPid = {-x-ahead-} xClock <= cMin   {-F-} && vcLessEqualImpl xRest y
                                                                  | xPid == yPid = {-compare-} xClock <= yClock       && vcLessEqualImpl xRest yRest
                                                                  | otherwise    = {-y-ahead-} cMin   <= yClock {-T-} && vcLessEqualImpl x     yRest
{-@ reflect vcLessEqualImpl @-}

-- |
vcLess :: VectorClock -> VectorClock -> Bool
vcLess a b = vcLessEqual a b && a /= b
{-@ inline vcLess @-}

-- |
-- >>> vcIndependent vcNew vcNew
-- True
vcIndependent :: VectorClock -> VectorClock -> Bool
vcIndependent a b = not (vcLess a b) && not (vcLess b a)
{-@ inline vcIndependent @-}


-- * Clocks

-- | Clocks range from 0.. because a pid might not have ticked yet, however 0
-- can't ever appear vector clock constructed with 'vcTick' because ticking
-- increments to 1.
{-@
type Clock = {clock:_ | cMin <= clock } @-}
type Clock = Integer

{-@
cMin :: Clock @-}
cMin :: Clock
cMin = 0
{-@ inline cMin @-}

-- | RealClocks range from 1.. because vector clocks count ticks, and after the
-- first 'vcTick' of a pid the clock counts one tick.
{-@
type RealClock = {clock:_ | rcMin <= clock } @-}
type RealClock = Integer

{-@
rcMin :: Clock @-}
rcMin :: Clock
rcMin = 1
{-@ inline rcMin @-}


-- * Show instances for tests

instance Show VectorClock where
    show (VectorClock vc) = show vc

instance Show p => Show (VCPoly p) where
    show Nil = "empty-vc"
    show VC{vcPid,vcClock,vcRest} = case vcRest of
        Nil -> this
        _ -> this ++ '\n' : show vcRest
      where
        this = show vcPid ++ ':' : 't' : show vcClock
