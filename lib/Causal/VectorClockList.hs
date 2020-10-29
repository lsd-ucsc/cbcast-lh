{-|
Description: Vector clocks implemented with associative lists keyed on UUIDs.
-}
{-# LANGUAGE NamedFieldPuns #-}
module Causal.VectorClockList
where

import Data.UUID (UUID)
import Language.Haskell.Liquid.ProofCombinators (impossible)

-- $setup
-- >>> import qualified Data.UUID as UUID
-- >>> import qualified Test.QuickCheck as QC
-- >>> instance QC.Arbitrary UUID where arbitrary = UUID.fromWords <$> QC.arbitrary <*> QC.arbitrary <*> QC.arbitrary <*> QC.arbitrary
-- >>> instance QC.Arbitrary p => QC.Arbitrary (VCPoly p) where arbitrary = QC.oneof [return Nil, VC <$> QC.arbitrary <*> QC.arbitrary <*> QC.arbitrary]
-- >>> instance QC.Arbitrary VectorClock where arbitrary = VectorClock <$> QC.arbitrary
-- >>> let cafe = UUID.fromWords 0xcafe 0xcafe 0xcafe 0xcafe
-- >>> let beef = UUID.fromWords 0xbeef 0xbeef 0xbeef 0xbeef
-- >>> let vc = VectorClock . foldr (uncurry VC) Nil


-- * Vector clocks

-- | Vector clock with polymorphic process-id and a refinement that guarantees
-- the clocks are naturals, the PIDs in-order, and consequently the PIDs are
-- unique.
data VCPoly pid
    = Nil
    | VC
        { vcPid     :: pid
        , vcClock   :: Integer
        , vcRest    :: VCPoly pid
        }
    deriving Eq
{-@
data VCPoly [vcpSize] _ where
      Nil :: _
    | VC
        :: pid:_
        -> {clock:_ | 0 <= clock }
        -> VCPoly {restPid:_ | pid < restPid}
        -> VCPoly _
@-}

-- | Concretely-typed vector clock carrying our refinement guarantees.
{-@
data VectorClock [vcSize] @-}
data VectorClock = VectorClock (VCPoly UUID)
    deriving Eq

-- |
-- >>> vcNew
-- empty-vc
vcNew :: VectorClock
vcNew = VectorClock Nil
-- |
-- >>> vcTick cafe vcNew
-- 0000cafe-0000-cafe-0000-cafe0000cafe:t1
-- >>> vcTick cafe $ vc [(cafe, 0), (beef, 0)]
-- 0000cafe-0000-cafe-0000-cafe0000cafe:t1
-- 0000beef-0000-beef-0000-beef0000beef:t0
-- >>> vcTick cafe $ vc [(beef, 3), (cafe, 4)]
-- 0000beef-0000-beef-0000-beef0000beef:t3
-- 0000cafe-0000-cafe-0000-cafe0000cafe:t5
--
-- prop> vcTick a (vcTick b vcNew) == vcTick b (vcTick a vcNew)
vcTick :: UUID -> VectorClock -> VectorClock
vcTick pid (VectorClock vc) = VectorClock (vcTickImpl pid vc)
vcTickImpl :: Ord p => p -> VCPoly p -> VCPoly p
vcTickImpl pid vc = let new = VC pid 1 Nil in case vc of
    VC{vcPid,vcClock,vcRest}
        | pid <  vcPid -> {-insert-} new{vcRest=vc{vcPid}} -- FIXME: LH requires that we prove vc has vcPid which is LT pid
        | pid == vcPid -> {-update-} vc{vcClock=vcClock + 1}
        | pid >  vcPid -> {-search-} vc{vcRest=vcTickImpl pid vcRest}
        | otherwise -> impossible "all cases are covered"
    Nil -> new
-- |
-- >>> let a = vc [(beef, 9)]
-- >>> let b = vc [(beef, 3), (cafe, 4)]
-- >>> vcCombine vcNew vcNew
-- empty-vc
-- >>> vcCombine a vcNew
-- 0000beef-0000-beef-0000-beef0000beef:t9
-- >>> vcCombine vcNew b
-- 0000beef-0000-beef-0000-beef0000beef:t3
-- 0000cafe-0000-cafe-0000-cafe0000cafe:t4
-- >>> vcCombine a b
-- 0000beef-0000-beef-0000-beef0000beef:t9
-- 0000cafe-0000-cafe-0000-cafe0000cafe:t4
--
-- prop> vcCombine a b == vcCombine b a
vcCombine :: VectorClock -> VectorClock -> VectorClock
vcCombine (VectorClock a) (VectorClock b) = VectorClock (vcCombineImpl a b)
{-@
vcCombineImpl :: a:_ -> b:_ -> {c:_ | vcpSize a + vcpSize b >= vcpSize c} / [vcpSize a + vcpSize b] @-}
vcCombineImpl :: Ord p => VCPoly p -> VCPoly p -> VCPoly p
vcCombineImpl Nil y   = y
vcCombineImpl x   Nil = x
vcCombineImpl x@(VC xPid xClock xRest) y@(VC yPid yClock yRest)
    | xPid < yPid = {-x ahead-} VC xPid xClock (vcCombineImpl xRest y{vcPid=yPid}) -- FIXME: LH requires that we prove y has yPid which is LT xPid
    | yPid < xPid = {-y ahead-} VC yPid yClock (vcCombineImpl yRest x{vcPid=xPid}) -- FIXME: LH requires that we prove x has xPid which is LT yPid
    | xPid == yPid = {-combine-} VC xPid (xClock `max` yClock) (vcCombineImpl xRest yRest)
    | otherwise = impossible "all cases are covered"

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

-- * Verification

{-@
vcSize :: _ -> Nat @-}
vcSize :: VectorClock -> Int
vcSize (VectorClock vc) = vcpSize vc
{-@ measure vcSize @-}

{-@
vcpSize :: _ -> Nat @-}
vcpSize :: VCPoly p -> Int
vcpSize Nil = 0
vcpSize VC{vcRest} = 1 + vcpSize vcRest
{-@ measure vcpSize @-}
