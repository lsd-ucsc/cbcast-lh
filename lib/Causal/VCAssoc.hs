module Causal.VectorClockLit where

-- import Language.Haskell.Liquid.ProofCombinators
--     (Proof, QED(..), (***), impossible)

-- $setup
-- >>> import qualified Data.UUID as UUID
-- >>> import qualified Test.QuickCheck as QC
-- >>> :{
-- instance Show pid => Show (VCAssoc pid) where
--     show xs = case xs of
--         Nil                 -> "empty-vc"
--         VC cur clock Nil    -> show cur ++ ':' : 't' : show clock
--         VC cur clock rest   -> show cur ++ ':' : 't' : show clock ++ '\n' : show rest
-- :}
--
-- >>> :{
-- instance QC.Arbitrary pid => QC.Arbitrary (VCAssoc pid) where
--     arbitrary = QC.oneof
--         [ return Nil
--         , VC <$> QC.arbitrary <*> QC.arbitrary <*> QC.arbitrary
--         ]
-- :}
--
-- >>> let beef = UUID.fromWords 0xbeef 0xbeef 0xbeef 0xbeef
-- >>> let cafe = UUID.fromWords 0xcafe 0xcafe 0xcafe 0xcafe
-- >>> let face = UUID.fromWords 0xface 0xface 0xface 0xface
-- >>> beef < cafe && cafe < face
-- True
-- >>> (#) = vcTick; infixr 5 #


-- * Types

type Clock = Integer
{-@ type     Clock = {c:Integer | cMin  <= c} @-}
{-@ type RealClock = {c:Integer | rcMin <= c} @-}

-- | Vector clock with polymorphic process-id and a refinement that guarantees
-- the clocks are valid, the PIDs in-order, and consequently the PIDs are
-- unique.
data VCAssoc pid
    = Nil
    | VC pid Clock (VCAssoc pid)
    deriving (Eq)
{-@
data VCAssoc [vcSize] pid
    = Nil
    | VC
        { p :: pid
        , c :: RealClock
        , r :: VCAssoc {p':pid | p < p'}
        }
@-}


-- * Clock values

-- | Clocks range on [0..∞) because vector clocks count ticks, but a pid might
-- not have ticked yet. This is the returned type.
{-@ inline cMin @-}
{-@ cMin :: Clock @-}
cMin :: Clock
cMin = 0

-- | RealClocks range on [1..∞) because vector clocks count ticks, and after
-- the first 'vcTick' of a pid the clock counts one tick. This is the stored
-- type.
{-@ inline rcMin @-}
{-@ rcMin :: RealClock @-}
rcMin :: Clock
rcMin = 1


-- * Logical predicates

{-@ measure vcSize @-}
{-@ vcSize :: VCAssoc pid -> Nat @-}
vcSize :: VCAssoc pid -> Int
vcSize Nil = 0
vcSize (VC _ _ vc) = 1 + vcSize vc

-- |
--
-- >>> larger 1 2
-- 2
-- >>> larger 2 1
-- 2
{-@ inline larger @-}
larger :: Ord a => a -> a -> a
larger a b = if a < b then b else a

-- |
--
-- Base cases.
--
-- >>> vcHasPid beef vcNew -- nil
-- False
-- >>> vcHasPid cafe (cafe # vcNew) -- found
-- True
--
-- Recursive cases.
--
-- >>> vcHasPid beef (cafe # vcNew) -- search, nil
-- False
-- >>> vcHasPid face (cafe # face # vcNew) -- search, found
-- True
--
-- QuickCheck properties.
--
-- prop> not $ vcHasPid pid vcNew
-- prop>       vcHasPid pid (pid # vcNew)
{-@ reflect vcHasPid @-}
vcHasPid :: Eq pid => pid -> VCAssoc pid -> Bool
vcHasPid pid Nil    = {-nil   -} False
vcHasPid pid (VC cur clock rest)
    | pid == cur    = {-found -} True
    | otherwise     = {-search-} vcHasPid pid rest


-- * User API 

-- |
--
-- >>> vcNew
-- empty-vc
{-@ inline vcNew @-}
vcNew :: VCAssoc pid
vcNew = Nil

-- |
--
-- These tests don't use vcTick to construct the vector clock because that's
-- what is under test.
--
-- Base cases.
--
-- >>> cafe `vcTick` Nil -- nil
-- 0000cafe-0000-cafe-0000-cafe0000cafe:t1
-- >>> beef `vcTick` (VC cafe rcMin Nil) -- insert
-- 0000beef-0000-beef-0000-beef0000beef:t1
-- 0000cafe-0000-cafe-0000-cafe0000cafe:t1
-- >>> cafe `vcTick` (VC cafe rcMin Nil) -- update
-- 0000cafe-0000-cafe-0000-cafe0000cafe:t2
--
-- Recursive cases.
--
-- >>> face `vcTick` (VC cafe rcMin Nil) -- search, nil
-- 0000cafe-0000-cafe-0000-cafe0000cafe:t1
-- 0000face-0000-face-0000-face0000face:t1
--
-- Longer test.
--
-- >>> cafe `vcTick` (VC beef rcMin . VC cafe rcMin . VC face rcMin $ Nil)
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
-- prop> not (vcHasPid pid v) ==> vcSize v + 1 == vcSize (vcTick pid v)
--
-- TODO: convert QC props to LH props or proofs
{-@ reflect vcTick @-}
vcTick :: Ord pid => pid -> VCAssoc pid -> VCAssoc pid
vcTick pid Nil      = {- nil  -} VC pid rcMin Nil
vcTick pid (VC cur clock rest)
    | pid <  cur    = {-insert-} VC pid rcMin (VC cur clock rest)
    | pid == cur    = {-update-} VC cur (clock+1) rest
    | otherwise     = {-search-} VC cur clock (vcTick pid rest)

-- |
--
-- Base cases.
--
-- >>> vcRead beef vcNew -- nil
-- 0
-- >>> vcRead cafe (cafe # vcNew) -- found
-- 1
--
-- Recursive cases.
--
-- >>> vcRead beef (cafe # vcNew) -- search, nil
-- 0
-- >>> vcRead face (cafe # face # vcNew) -- search, found
-- 1
--
-- QuickCheck properties.
--
-- prop> 0 == vcRead pid vcNew
-- prop> 1 == vcRead pid (pid # vcNew)
--
-- TODO: convert QC props to LH props or proofs
{-@ reflect vcRead @-}
{-@ vcRead :: _ -> _ -> Clock @-}
vcRead :: Ord pid => pid -> VCAssoc pid -> Clock
vcRead _ Nil = cMin
vcRead pid (VC cur clock rest)
    | pid == cur    = clock
    | otherwise     = vcRead pid rest

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
--
-- TODO: convert QC props to LH props or proofs
{-@ reflect vcCombine @-}
{-@ vcCombine :: a:_ -> b:_ -> _ / [vcSize a + vcSize b] @-}
vcCombine :: Ord pid => VCAssoc pid -> VCAssoc pid -> VCAssoc pid
vcCombine x   Nil   = {- x&nil -} x
vcCombine Nil y     = {- nil&y -} y
vcCombine (VC xPid xClock xRest) (VC yPid yClock yRest)
    | xPid <  yPid  = {-x-ahead-} VC xPid  xClock                  (vcCombine xRest (VC yPid yClock yRest))
    | xPid == yPid  = {-combine-} VC xPid (xClock `larger` yClock) (vcCombine xRest yRest)
    | otherwise     = {-y-ahead-} VC yPid                  yClock  (vcCombine (VC xPid xClock xRest) yRest)

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
-- >>> vcLessEqual (VC beef cMin Nil) vcNew -- y-nil, nil-nil (invalid data flips the result: 0 <= 0 is true)
-- True
--
-- >>> vcLessEqual vcNew (beef # vcNew) -- x-nil, nil-nil (always true because absent values are zero: 0 <= 1 is true)
-- True
-- >>> vcLessEqual vcNew (VC beef cMin Nil) -- x-nil, nil-nil (invalid data: 0 <= 0 is still true)
-- True
-- >>> vcLessEqual vcNew (VC beef (cMin-1) Nil) -- x-nil, nil-nil (invalid data flips the result: 0 <= -1 is false)
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
{-@ reflect vcLessEqual @-}
{-@ vcLessEqual :: a:_ -> b:_ -> _ / [vcSize a + vcSize b] @-}
vcLessEqual :: Ord pid => VCAssoc pid -> VCAssoc pid -> Bool
vcLessEqual Nil Nil                 = {- equal  -} True
vcLessEqual (VC _ xClock xRest) Nil = {- x<=nil -} xClock <= cMin   {-False-} && vcLessEqual xRest Nil
vcLessEqual Nil (VC _ yClock yRest) = {- nil<=y -} cMin   <= yClock {-True -} && vcLessEqual Nil yRest
vcLessEqual x@(VC xPid xClock xRest) y@(VC yPid yClock yRest)
    | xPid <  yPid  = {-x-ahead-} xClock <= cMin   {-False-} && vcLessEqual xRest y
    | xPid == yPid  = {-compare-} xClock <= yClock           && vcLessEqual xRest yRest
    | otherwise     = {-y-ahead-} cMin   <= yClock {-True -} && vcLessEqual x     yRest

{-@ inline vcLess @-}
vcLess :: Ord pid => VCAssoc pid -> VCAssoc pid -> Bool
vcLess a b = vcLessEqual a b && a /= b

-- |
-- >>> vcIndependent vcNew vcNew
-- True
{-@ inline vcIndependent @-}
vcIndependent :: Ord pid => VCAssoc pid -> VCAssoc pid -> Bool
vcIndependent a b = not (vcLess a b) && not (vcLess b a)
