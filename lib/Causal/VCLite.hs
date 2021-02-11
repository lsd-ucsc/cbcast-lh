-- | Implementation of vector clocks over polymorphic PIDs using a pair of a
-- PID list and a Clock list constrained to have the same lengths.
--
-- Functions operating on pairs of VCs constrain those to have the same list of
-- PIDs.
module Causal.VCLite where

import Redefined (listLength, listElem, impossibleConst)

-- $setup
-- >>> import Data.List (elemIndex, intercalate)
-- >>> import Data.Maybe (fromMaybe)
-- >>> import Data.Typeable (Typeable(..), typeOf)
-- >>> :{
-- instance Show pid => Show (VC pid) where
--     show (VC [] []) = "empty-vc"
--     show (VC pids clocks)
--         | length pids == length clocks = intercalate "\n" $ zipWith item pids clocks
--         | otherwise = error "pids length must equal clocks length"
--       where
--         item pid clock = show pid ++ ':':'t':show clock
-- :}
--
-- >>> :{
-- instance (Typeable a, Typeable b) => Show (a -> b) where
--     show = show . typeOf
-- :}
--
-- >>> import qualified Test.QuickCheck as QC
-- >>> :{
-- instance QC.Arbitrary pid => QC.Arbitrary (VC pid) where
--     arbitrary = do
--         pids <- QC.arbitrary
--         clocks <- QC.arbitrary
--         let m = length pids `min` length clocks
--         return $ VC (take m pids) (take m clocks)
-- :}
--
-- >>> import qualified Data.UUID as UUID
-- >>> let beef = UUID.fromWords 0xbeef 0xbeef 0xbeef 0xbeef
-- >>> let cafe = UUID.fromWords 0xcafe 0xcafe 0xcafe 0xcafe
-- >>> let face = UUID.fromWords 0xface 0xface 0xface 0xface
-- >>> beef < cafe && cafe < face
-- True
-- >>> (#) = vcTick; infixr 5 #


-- * Types

type Clock = Integer
{-@ type Clock = {c:Integer | cMin <= c} @-}

data VC pid
    = VC [pid] [Clock]
    deriving Eq
{-@
data VC pid
    = VC
        { pids :: [pid]
        , clocks :: {cs:[Clock] | len pids == len cs}
        }
@-}


-- * Clock values

-- | Clocks range on [0..∞) because vector clocks count ticks, but a pid might
-- not have ticked yet.
{-@ inline cMin @-}
{-@ cMin :: Clock @-}
cMin :: Clock
cMin = 0


-- * Internals


-- * Generic

-- | Implementation of 'replicate' lifted to specifications. Probably same as
-- that of 'Prelude'.
--
-- prop> replicate n x == listReplicate n x
{-@ reflect listReplicate @-}
{-@ listReplicate :: n:Nat -> a -> {xs:[a] | n == len xs} @-}
listReplicate :: Int -> a -> [a]
listReplicate n x
    | n <= 0    = []
    | otherwise = x:listReplicate (n-1) x

-- | Similar to @base:Data.List.elemIndex@ or
-- @containers:Data.Sequence.elemeIndexL@, "elemIndexL finds the leftmost index
-- of the specified element, if it is present, and otherwise Nothing," but
-- disallows searching for elements that aren't contained.
--
-- >>> listElemIndex 'r' "world"
-- 2
-- >>> listElemIndex 'q' "world" -- this case eliminated by LH precondition
-- 5
--
-- prop> elem a xs ==> elemIndex a xs == Just (listElemIndex a xs)
{-@ reflect listElemIndex @-}
{-@ ple listElemIndex @-}
{-@ listElemIndex :: x:a -> {xs:[a] | listElem x xs} -> {n:Nat | n < len xs} @-}
listElemIndex :: Eq a => a -> [a] -> Int
listElemIndex _ [] = impossibleConst 0 "listElem x xs"
listElemIndex a (x:xs)
    | a == x    = 0
    | otherwise = 1 + listElemIndex a xs

-- | Implementation of '!!' lifted to specifications. Similar to that of
-- 'Prelude'. Instead of errors for out of range indexes, the precondition
-- requires that the index `n` is in the list `xs`. A default value is required
-- to lift to specifications, but it will never be used.
--
-- >>> listGetIndex "world" 2
-- Just 'r'
-- >>> listGetIndex "world" 20 -- this case eliminated by LH precondition
-- Nothing
-- >>> listGetIndex "world" (-2) -- this case eliminated by LH precondition
-- Nothing
--
-- prop> 0 <= n && n < length xs ==> Just (xs !! n) == listGetIndex xs n
{-@ reflect listGetIndex @-}
{-@ listGetIndex :: xs:[a] -> {n:Nat | n < len xs} -> {m:Maybe a | isJust m} @-}
listGetIndex :: [a] -> Int -> Maybe a
listGetIndex [] _ = impossibleConst Nothing "0 <= n < len xs"
listGetIndex (x:xs) n
    | n == 0    = Just x
    | otherwise = listGetIndex xs (n-1)

-- | Set the value at index.
--
-- >>> listSetIndex "world" '#' 2
-- "wo#ld"
-- >>> listSetIndex "world" '#' 20 -- this case eliminated by LH precondition
-- "world"
-- >>> listSetIndex "world" '#' (-2) -- this case eliminated by LH precondition
-- "world"
--
{-@ reflect listSetIndex @-}
{-@ listSetIndex :: xs:[a] -> a -> {n:Nat | n < len xs} -> {ys:[a] | len xs == len ys} @-}
listSetIndex :: [a] -> a -> Int -> [a]
listSetIndex [] _ _ = impossibleConst [] "0 <= n < len xs"
listSetIndex (x:xs) a n
    | n == 0    = a:xs
    | otherwise = x:listSetIndex xs a (n-1)

-- | Implementation of 'fromJust' lifted to specifications. Probably same as
-- that of 'Prelude'.
--
-- >>> maybeFromJust '!' (Just 'a')
-- 'a'
-- >>> maybeFromJust '!' Nothing -- this case eliminated by LH precondition
-- '!'
--
-- prop> fromMaybe def m == maybeFromJust def m
{-@ inline maybeFromJust @-}
{-@ maybeFromJust :: a -> {m:Maybe a | isJust m} -> a @-}
maybeFromJust :: a -> Maybe a -> a
maybeFromJust _ (Just x) = x
maybeFromJust x Nothing = impossibleConst x "isJust m"

-- | Implementation of 'zipWith' lifted to specifications. Probably same as
-- that of 'Prelude' but disallows lists of unequal length.
--
-- prop> zipWith f ys zs == listZipWith f ys zs
{-@ listZipWith :: (a -> b -> c) -> xs:[a] -> {ys:[b] | len xs == len ys} -> {zs:[c] | len xs == len zs && len ys == len zs} @-}
listZipWith :: (a -> b -> c) -> [a] -> [b] -> [c]
listZipWith f (x:xs) (y:ys) = f x y:listZipWith f xs ys
listZipWith _ [] [] = []
listZipWith _ _ _ = impossibleConst [] "lists have same length"


-- ** Specific

-- |
--
-- >>> vcHasPid beef $ VC [] []
-- False
-- >>> vcHasPid cafe $ VC [cafe] [cMin]
-- True
-- >>> vcHasPid beef $ VC [cafe] [cMin]
-- False
-- >>> vcHasPid face $ VC [cafe, face] [cMin, cMin]
-- True
--
-- QuickCheck properties.
--
-- prop> pid `elem` pids ==> pid `vcHasPid` vcNew pids
{-@ inline vcHasPid @-}
vcHasPid :: Eq pid => pid -> VC pid -> Bool
vcHasPid pid (VC pids _) = listElem pid pids

-- |
--
-- >>> VC [] [] `vcPidsMatch` VC [] []
-- True
-- >>> VC [cafe] [] `vcPidsMatch` VC [] []
-- False
-- >>> VC [] [] `vcPidsMatch` VC [cafe] []
-- False
-- >>> VC [cafe] [] `vcPidsMatch` VC [cafe] []
-- True
--
{-@ inline vcPidsMatch @-}
vcPidsMatch :: Eq pid => VC pid -> VC pid -> Bool
vcPidsMatch (VC aPids _) (VC bPids _) = aPids == bPids

-- |
--
-- >>> [] `vcCombineClocks` []
-- []
-- >>> [1, 2, 0] `vcCombineClocks` [0, 4, 1]
-- [1,4,1]
--
{-@ reflect vcCombineClocks @-}
{-@ vcCombineClocks :: xs:[Clock] -> {ys:[Clock] | len xs == len ys} -> {zs:[Clock] | len xs == len zs && len ys == len zs} @-}
vcCombineClocks :: [Clock] -> [Clock] -> [Clock]
vcCombineClocks (x:xs) (y:ys) = (if x < y then y else x):vcCombineClocks xs ys
vcCombineClocks [] [] = []
vcCombineClocks _ _ = impossibleConst [] "lists have same length"

-- |
--
-- >>> [] `vcLessEqualClocks` []
-- True
-- >>> [1, 2, 0] `vcLessEqualClocks` [2, 2, 0]
-- True
-- >>> [1, 2, 4] `vcLessEqualClocks` [2, 2, 0]
-- False
--
{-@ reflect vcLessEqualClocks @-}
{-@ vcLessEqualClocks :: xs:[Clock] -> {ys:[Clock] | len xs == len ys} -> Bool @-}
vcLessEqualClocks :: [Clock] -> [Clock] -> Bool
vcLessEqualClocks (x:xs) (y:ys) = x <= y && vcLessEqualClocks xs ys
vcLessEqualClocks [] [] = True
vcLessEqualClocks _ _ = impossibleConst False "lists have same length"


-- * User API

-- |
--
-- >>> vcNew []
-- empty-vc
-- >>> vcNew [cafe, face]
-- 0000cafe-0000-cafe-0000-cafe0000cafe:t0
-- 0000face-0000-face-0000-face0000face:t0
--
{-@ inline vcNew @-}
vcNew :: [pid] -> VC pid
vcNew pids = VC pids $ listReplicate (listLength pids) 0

-- |
--
-- >>> vcRead beef $ vcNew [] -- this case eliminated by LH precondition
-- 0
-- >>> vcRead cafe $ vcNew [cafe]
-- 0
--
-- Recursive cases.
--
-- >>> vcRead beef (cafe # vcNew [cafe]) -- this case eliminated by LH precondition
-- 0
-- >>> vcRead face (cafe # face # vcNew [cafe, face])
-- 1
--
-- QuickCheck properties.
--
-- prop> 0 == vcRead pid (vcNew [])
-- prop> 1 == vcRead pid (pid # vcNew [pid])
--
{-@ inline vcRead @-}
{-@ vcRead :: p:pid -> {vc:VC pid | vcHasPid p vc} -> Clock @-}
vcRead :: Eq pid => pid -> VC pid -> Clock
vcRead pid (VC pids clocks)
    = maybeFromJust 0 $ listGetIndex clocks (listElemIndex pid pids)

-- |
--
-- >>> cafe `vcTick` VC [cafe] [1] -- update
-- 0000cafe-0000-cafe-0000-cafe0000cafe:t2
--
-- >>> cafe `vcTick` VC [beef, cafe, face] [1, 1, 1]
-- 0000beef-0000-beef-0000-beef0000beef:t1
-- 0000cafe-0000-cafe-0000-cafe0000cafe:t2
-- 0000face-0000-face-0000-face0000face:t1
--
-- >>> beef # beef # cafe # vcNew [beef, cafe, face]
-- 0000beef-0000-beef-0000-beef0000beef:t2
-- 0000cafe-0000-cafe-0000-cafe0000cafe:t1
-- 0000face-0000-face-0000-face0000face:t0
-- >>> cafe # cafe # vcNew [beef, cafe, face]
-- 0000beef-0000-beef-0000-beef0000beef:t0
-- 0000cafe-0000-cafe-0000-cafe0000cafe:t2
-- 0000face-0000-face-0000-face0000face:t0
--
-- QuickCheck property showing that the result is the same regardless of the
-- order of ticks.
--
-- prop> vcTick a (vcTick b $ vcNew [a, b]) == vcTick b (vcTick a $ vcNew [a, b])
{-@ inline vcTick @-}
{-@ vcTick :: p:pid -> {vc:VC pid | vcHasPid p vc} -> VC pid @-}
vcTick :: Eq pid => pid -> VC pid -> VC pid
vcTick pid (VC pids clocks) = VC pids $ listSetIndex clocks (clock+1) index
  where
    index = listElemIndex pid pids
    clock = maybeFromJust 0 $ listGetIndex clocks index

-- |
--
-- >>> vcCombine (vcNew []) (vcNew [])
-- empty-vc
--
-- >>> vcCombine (cafe # vcNew [cafe]) (cafe # vcNew [cafe]) -- compare
-- 0000cafe-0000-cafe-0000-cafe0000cafe:t1
-- >>> vcCombine (cafe # cafe # vcNew [cafe]) (cafe # vcNew [cafe]) -- compare
-- 0000cafe-0000-cafe-0000-cafe0000cafe:t2
-- >>> vcCombine (cafe # vcNew [cafe]) (cafe # cafe # vcNew [cafe]) -- compare
-- 0000cafe-0000-cafe-0000-cafe0000cafe:t2
--
-- >>> vcCombine (beef # beef # cafe # vcNew [beef, cafe, face]) (cafe # cafe # vcNew [beef, cafe, face]) -- compare
-- 0000beef-0000-beef-0000-beef0000beef:t2
-- 0000cafe-0000-cafe-0000-cafe0000cafe:t2
-- 0000face-0000-face-0000-face0000face:t0
--
-- QuickCheck property for commutativity.
--
-- prop> let a = VC pids aClocks; b = VC pids bClocks in vcCombine a b == vcCombine b a
{-@ inline vcCombine @-}
{-@ vcCombine :: a:VC pid -> {b:VC pid | vcPidsMatch a b} -> {c:VC pid | vcPidsMatch a c && vcPidsMatch b c} @-}
vcCombine :: VC pid -> VC pid -> VC pid
vcCombine (VC aPids aClocks) (VC _ bClocks)
    = VC aPids $ vcCombineClocks aClocks bClocks

-- |
--
-- >>> vcLessEqual (vcNew []) (vcNew []) -- nil-nil
-- True
--
-- >>> vcLessEqual (cafe # vcNew [cafe]) (cafe # vcNew [cafe]) -- compare
-- True
-- >>> vcLessEqual (cafe # cafe # vcNew [cafe]) (cafe # vcNew [cafe]) -- compare
-- False
-- >>> vcLessEqual (cafe # vcNew [cafe]) (cafe # cafe # vcNew [cafe]) -- compare
-- True
--
-- >>> vcLessEqual (beef # cafe # face # vcNew [beef, cafe, face]) (beef # cafe # face # vcNew [beef, cafe, face])
-- True
-- >>> vcLessEqual (beef # cafe # face # vcNew [beef, cafe, face]) (beef # face # vcNew [beef, cafe, face])
-- False
-- >>> vcLessEqual (beef # face # vcNew [beef, cafe, face]) (beef # cafe # face # vcNew [beef, cafe, face])
-- True
{-@ inline vcLessEqual @-}
{-@ vcLessEqual :: a:VC pid -> {b:VC pid | vcPidsMatch a b} -> Bool @-}
vcLessEqual :: VC pid -> VC pid -> Bool
vcLessEqual (VC _ aClocks) (VC _ bClocks)
    = vcLessEqualClocks aClocks bClocks

{-@ inline vcLess @-}
{-@ vcLess :: a:VC pid -> {b:VC pid | vcPidsMatch a b} -> Bool @-}
vcLess :: Eq pid => VC pid -> VC pid -> Bool
vcLess a b = vcLessEqual a b && a /= b

-- |
--
-- >>> vcIndependent (vcNew []) (vcNew [])
-- True
{-@ inline vcIndependent @-}
{-@ vcIndependent :: a:VC pid -> {b:VC pid | vcPidsMatch a b} -> Bool @-}
vcIndependent :: Eq pid => VC pid -> VC pid -> Bool
vcIndependent a b = not (vcLess a b) && not (vcLess b a)
