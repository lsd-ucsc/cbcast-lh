-- | Implementation of vector clocks over polymorphic PIDs using an explicit
-- association-list ADT with a strict ordering on PID values.
module Causal.VCAssoc where

-- import Language.Haskell.Liquid.ProofCombinators
--     (Proof, QED(..), (***), impossible)

-- $setup
-- >>> import qualified Data.UUID as UUID
-- >>> import qualified Test.QuickCheck as QC
-- >>> :{
-- instance Show pid => Show (VCAssoc pid) where
--     show xs = case xs of
--         Nil                  -> "empty-vc"
--         VCA cur clock Nil    -> show cur ++ ':' : 't' : show clock
--         VCA cur clock rest   -> show cur ++ ':' : 't' : show clock ++ '\n' : show rest
-- :}
--
-- >>> :{
-- instance QC.Arbitrary pid => QC.Arbitrary (VCAssoc pid) where
--     arbitrary = QC.oneof
--         [ return Nil
--         , VCA <$> QC.arbitrary <*> QC.arbitrary <*> QC.arbitrary
--         ]
-- :}
--
-- >>> let beef = UUID.fromWords 0xbeef 0xbeef 0xbeef 0xbeef
-- >>> let cafe = UUID.fromWords 0xcafe 0xcafe 0xcafe 0xcafe
-- >>> let face = UUID.fromWords 0xface 0xface 0xface 0xface
-- >>> beef < cafe && cafe < face
-- True
-- >>> (#) = vcaTick; infixr 5 #


-- * Types

type Clock = Integer
{-@ type     Clock = {c:Integer | cMin  <= c} @-}
{-@ type RealClock = {c:Integer | rcMin <= c} @-}

-- | Vector clock with polymorphic process-id and a refinement that guarantees
-- the clocks are valid, the PIDs in-order, and consequently the PIDs are
-- unique.
data VCAssoc pid
    = Nil
    | VCA pid Clock (VCAssoc pid)
    deriving (Eq)
{-@
data VCAssoc pid
    = Nil
    | VCA
        { p :: pid
        , c :: RealClock
        , r :: VCAssoc {p':pid | p < p'}
        }
@-}
-- FIXME add termination measure [vcaSize]; LH rejects it for some reason


-- * Clock values

-- | Clocks range on [0..∞) because vector clocks count ticks, but a pid might
-- not have ticked yet. This is the returned type.
{-@ inline cMin @-}
{-@ cMin :: Clock @-}
cMin :: Clock
cMin = 0

-- | RealClocks range on [1..∞) because vector clocks count ticks, and after
-- the first 'vcaTick' of a pid the clock counts one tick. This is the stored
-- type.
{-@ inline rcMin @-}
{-@ rcMin :: RealClock @-}
rcMin :: Clock
rcMin = 1


-- * Logical predicates

{-@ measure vcaSize @-}
{-@ vcaSize :: VCAssoc pid -> Nat @-}
vcaSize :: VCAssoc pid -> Int
vcaSize Nil = 0
vcaSize (VCA _ _ rest) = 1 + vcaSize rest

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
-- >>> vcaHasPid beef vcaNew -- nil
-- False
-- >>> vcaHasPid cafe (cafe # vcaNew) -- found
-- True
--
-- Recursive cases.
--
-- >>> vcaHasPid beef (cafe # vcaNew) -- search, nil
-- False
-- >>> vcaHasPid face (cafe # face # vcaNew) -- search, found
-- True
--
-- QuickCheck properties.
--
-- prop> not $ vcaHasPid pid vcaNew
-- prop>       vcaHasPid pid (pid # vcaNew)
{-@ reflect vcaHasPid @-}
vcaHasPid :: Eq pid => pid -> VCAssoc pid -> Bool
vcaHasPid pid Nil    = {-nil   -} False
vcaHasPid pid (VCA cur clock rest)
    | pid == cur    = {-found -} True
    | otherwise     = {-search-} vcaHasPid pid rest


-- * User API 

-- |
--
-- >>> vcaNew
-- empty-vc
{-@ inline vcaNew @-}
vcaNew :: VCAssoc pid
vcaNew = Nil

-- |
--
-- These tests don't use vcaTick to construct the vector clock because that's
-- what is under test.
--
-- Base cases.
--
-- >>> cafe `vcaTick` Nil -- nil
-- 0000cafe-0000-cafe-0000-cafe0000cafe:t1
-- >>> beef `vcaTick` (VCA cafe rcMin Nil) -- insert
-- 0000beef-0000-beef-0000-beef0000beef:t1
-- 0000cafe-0000-cafe-0000-cafe0000cafe:t1
-- >>> cafe `vcaTick` (VCA cafe rcMin Nil) -- update
-- 0000cafe-0000-cafe-0000-cafe0000cafe:t2
--
-- Recursive cases.
--
-- >>> face `vcaTick` (VCA cafe rcMin Nil) -- search, nil
-- 0000cafe-0000-cafe-0000-cafe0000cafe:t1
-- 0000face-0000-face-0000-face0000face:t1
--
-- Longer test.
--
-- >>> cafe `vcaTick` (VCA beef rcMin . VCA cafe rcMin . VCA face rcMin $ Nil)
-- 0000beef-0000-beef-0000-beef0000beef:t1
-- 0000cafe-0000-cafe-0000-cafe0000cafe:t2
-- 0000face-0000-face-0000-face0000face:t1
--
-- QuickCheck property showing that the result is the same regardless of the
-- order of ticks.
--
-- prop> vcaTick a (vcaTick b vcaNew) == vcaTick b (vcaTick a vcaNew)
--
-- QuickCheck property showing how the presence of a pid relates to vc size
-- after a tick.
--
-- prop> vcaSize (vcaTick pid v) == vcaSize (vcaTick pid (vcaTick pid v))
-- prop> not (vcaHasPid pid v) ==> vcaSize v + 1 == vcaSize (vcaTick pid v)
--
-- TODO: convert QC props to LH props or proofs
{-@ reflect vcaTick @-}
vcaTick :: Ord pid => pid -> VCAssoc pid -> VCAssoc pid
vcaTick pid Nil      = {- nil  -} VCA pid rcMin Nil
vcaTick pid (VCA cur clock rest)
    | pid <  cur    = {-insert-} VCA pid rcMin (VCA cur clock rest)
    | pid == cur    = {-update-} VCA cur (clock+1) rest
    | otherwise     = {-search-} VCA cur clock (vcaTick pid rest)

-- |
--
-- Base cases.
--
-- >>> vcaRead beef vcaNew -- nil
-- 0
-- >>> vcaRead cafe (cafe # vcaNew) -- found
-- 1
--
-- Recursive cases.
--
-- >>> vcaRead beef (cafe # vcaNew) -- search, nil
-- 0
-- >>> vcaRead face (cafe # face # vcaNew) -- search, found
-- 1
--
-- QuickCheck properties.
--
-- prop> 0 == vcaRead pid vcaNew
-- prop> 1 == vcaRead pid (pid # vcaNew)
--
-- TODO: convert QC props to LH props or proofs
{-@ reflect vcaRead @-}
{-@ vcaRead :: _ -> _ -> Clock @-}
vcaRead :: Ord pid => pid -> VCAssoc pid -> Clock
vcaRead _ Nil = cMin
vcaRead pid (VCA cur clock rest)
    | pid == cur    = clock
    | otherwise     = vcaRead pid rest

-- |
--
-- Base cases.
--
-- >>> vcaCombine vcaNew (beef # vcaNew) -- x-nil
-- 0000beef-0000-beef-0000-beef0000beef:t1
-- >>> vcaCombine (beef # vcaNew) vcaNew -- y-nil
-- 0000beef-0000-beef-0000-beef0000beef:t1
--
-- Recursive cases.
--
-- >>> vcaCombine (beef # vcaNew) (cafe # vcaNew) -- x-ahead, x-nil
-- 0000beef-0000-beef-0000-beef0000beef:t1
-- 0000cafe-0000-cafe-0000-cafe0000cafe:t1
-- >>> vcaCombine (cafe # vcaNew) (cafe # vcaNew) -- compare, x-nil
-- 0000cafe-0000-cafe-0000-cafe0000cafe:t1
-- >>> vcaCombine (cafe # cafe # vcaNew) (cafe # vcaNew) -- compare, x-nil (left is larger)
-- 0000cafe-0000-cafe-0000-cafe0000cafe:t2
-- >>> vcaCombine (cafe # vcaNew) (cafe # cafe # vcaNew) -- compare, x-nil (right is larger)
-- 0000cafe-0000-cafe-0000-cafe0000cafe:t2
-- >>> vcaCombine (face # vcaNew) (cafe # vcaNew) -- y-ahead, y-nil
-- 0000cafe-0000-cafe-0000-cafe0000cafe:t1
-- 0000face-0000-face-0000-face0000face:t1
--
-- QuickCheck property for commutativity.
--
-- prop> vcaCombine a b == vcaCombine b a
--
-- TODO: convert QC props to LH props or proofs
{-@ reflect vcaCombine @-}
{-@ vcaCombine :: a:_ -> b:_ -> _ / [vcaSize a + vcaSize b] @-}
vcaCombine :: Ord pid => VCAssoc pid -> VCAssoc pid -> VCAssoc pid
vcaCombine x   Nil   = {- x&nil -} x
vcaCombine Nil y     = {- nil&y -} y
vcaCombine (VCA xPid xClock xRest) (VCA yPid yClock yRest)
    | xPid <  yPid  = {-x-ahead-} VCA xPid  xClock                  (vcaCombine xRest (VCA yPid yClock yRest))
    | xPid == yPid  = {-combine-} VCA xPid (xClock `larger` yClock) (vcaCombine xRest yRest)
    | otherwise     = {-y-ahead-} VCA yPid                  yClock  (vcaCombine (VCA xPid xClock xRest) yRest)

-- |
--
-- Base cases.
--
-- >>> vcaLessEqual vcaNew vcaNew -- nil-nil
-- True
--
-- Boring recursive cases.
--
-- >>> vcaLessEqual (beef # vcaNew) vcaNew -- y-nil, nil-nil (always false because absent values are zero: 1 <= 0 is false)
-- False
-- >>> vcaLessEqual (VCA beef cMin Nil) vcaNew -- y-nil, nil-nil (invalid data flips the result: 0 <= 0 is true)
-- True
--
-- >>> vcaLessEqual vcaNew (beef # vcaNew) -- x-nil, nil-nil (always true because absent values are zero: 0 <= 1 is true)
-- True
-- >>> vcaLessEqual vcaNew (VCA beef cMin Nil) -- x-nil, nil-nil (invalid data: 0 <= 0 is still true)
-- True
-- >>> vcaLessEqual vcaNew (VCA beef (cMin-1) Nil) -- x-nil, nil-nil (invalid data flips the result: 0 <= -1 is false)
-- False
--
-- Recursive cases.
--
-- >>> vcaLessEqual (beef # vcaNew) (cafe # vcaNew) -- x-ahead, x-nil
-- False
-- >>> vcaLessEqual (beef # cafe # vcaNew) (cafe # vcaNew) -- x-ahead, compare, nil-nil
-- False
-- >>> vcaLessEqual (cafe # vcaNew) (cafe # vcaNew) -- compare, nil-nil
-- True
-- >>> vcaLessEqual (cafe # cafe # vcaNew) (cafe # vcaNew) -- compare, nil-nil (left is larger: 2 <= 1 is false)
-- False
-- >>> vcaLessEqual (cafe # vcaNew) (cafe # cafe # vcaNew) -- compare, nil-nil (right is larger: 1 <= 2 is true)
-- True
-- >>> vcaLessEqual (face # vcaNew) (cafe # vcaNew) -- y-ahead, y-nil
-- False
--
-- Longer test.
--
-- >>> vcaLessEqual (beef # cafe # face # vcaNew) (beef # cafe # face # vcaNew)
-- True
-- >>> vcaLessEqual (beef # cafe # face # vcaNew) (beef # face # vcaNew)
-- False
-- >>> vcaLessEqual (beef # face # vcaNew) (beef # cafe # face # vcaNew)
-- True
{-@ reflect vcaLessEqual @-}
{-@ vcaLessEqual :: a:_ -> b:_ -> _ / [vcaSize a + vcaSize b] @-}
vcaLessEqual :: Ord pid => VCAssoc pid -> VCAssoc pid -> Bool
vcaLessEqual Nil Nil                 = {- equal  -} True
vcaLessEqual (VCA _ xClock xRest) Nil = {- x<=nil -} xClock <= cMin   {-False-} && vcaLessEqual xRest Nil
vcaLessEqual Nil (VCA _ yClock yRest) = {- nil<=y -} cMin   <= yClock {-True -} && vcaLessEqual Nil yRest
vcaLessEqual x@(VCA xPid xClock xRest) y@(VCA yPid yClock yRest)
    | xPid <  yPid  = {-x-ahead-} xClock <= cMin   {-False-} && vcaLessEqual xRest y
    | xPid == yPid  = {-compare-} xClock <= yClock           && vcaLessEqual xRest yRest
    | otherwise     = {-y-ahead-} cMin   <= yClock {-True -} && vcaLessEqual x     yRest

{-@ inline vcaLess @-}
vcaLess :: Ord pid => VCAssoc pid -> VCAssoc pid -> Bool
vcaLess a b = vcaLessEqual a b && a /= b

-- |
-- >>> vcaIndependent vcaNew vcaNew
-- True
{-@ inline vcaIndependent @-}
vcaIndependent :: Ord pid => VCAssoc pid -> VCAssoc pid -> Bool
vcaIndependent a b = not (vcaLess a b) && not (vcaLess b a)
