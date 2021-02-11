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
-- instance Show pid => Show (VCL pid) where
--     show (VCL [] []) = "empty-vc"
--     show (VCL pids clocks)
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
-- instance QC.Arbitrary pid => QC.Arbitrary (VCL pid) where
--     arbitrary = do
--         pids <- QC.arbitrary
--         clocks <- QC.arbitrary
--         let m = length pids `min` length clocks
--         return $ VCL (take m pids) (take m clocks)
-- :}
--
-- >>> import qualified Data.UUID as UUID
-- >>> let beef = UUID.fromWords 0xbeef 0xbeef 0xbeef 0xbeef
-- >>> let cafe = UUID.fromWords 0xcafe 0xcafe 0xcafe 0xcafe
-- >>> let face = UUID.fromWords 0xface 0xface 0xface 0xface
-- >>> beef < cafe && cafe < face
-- True
-- >>> (#) = vclTick; infixr 5 #


-- * Types

type Clock = Integer
{-@ type Clock = {c:Integer | cMin <= c} @-}

data VCL pid
    = VCL [pid] [Clock]
    deriving Eq
{-@
data VCL pid
    = VCL
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
-- >>> vclHasPid beef $ VCL [] []
-- False
-- >>> vclHasPid cafe $ VCL [cafe] [cMin]
-- True
-- >>> vclHasPid beef $ VCL [cafe] [cMin]
-- False
-- >>> vclHasPid face $ VCL [cafe, face] [cMin, cMin]
-- True
--
-- QuickCheck properties.
--
-- prop> pid `elem` pids ==> pid `vclHasPid` vclNew pids
{-@ inline vclHasPid @-}
vclHasPid :: Eq pid => pid -> VCL pid -> Bool
vclHasPid pid (VCL pids _) = listElem pid pids

-- |
--
-- >>> VCL [] [] `vclPidsMatch` VCL [] []
-- True
-- >>> VCL [cafe] [] `vclPidsMatch` VCL [] []
-- False
-- >>> VCL [] [] `vclPidsMatch` VCL [cafe] []
-- False
-- >>> VCL [cafe] [] `vclPidsMatch` VCL [cafe] []
-- True
--
{-@ inline vclPidsMatch @-}
vclPidsMatch :: Eq pid => VCL pid -> VCL pid -> Bool
vclPidsMatch (VCL aPids _) (VCL bPids _) = aPids == bPids

-- |
--
-- >>> [] `vclCombineClocks` []
-- []
-- >>> [1, 2, 0] `vclCombineClocks` [0, 4, 1]
-- [1,4,1]
--
{-@ reflect vclCombineClocks @-}
{-@ vclCombineClocks :: xs:[Clock] -> {ys:[Clock] | len xs == len ys} -> {zs:[Clock] | len xs == len zs && len ys == len zs} @-}
vclCombineClocks :: [Clock] -> [Clock] -> [Clock]
vclCombineClocks (x:xs) (y:ys) = (if x < y then y else x):vclCombineClocks xs ys
vclCombineClocks [] [] = []
vclCombineClocks _ _ = impossibleConst [] "lists have same length"

-- |
--
-- >>> [] `vclLessEqualClocks` []
-- True
-- >>> [1, 2, 0] `vclLessEqualClocks` [2, 2, 0]
-- True
-- >>> [1, 2, 4] `vclLessEqualClocks` [2, 2, 0]
-- False
--
{-@ reflect vclLessEqualClocks @-}
{-@ vclLessEqualClocks :: xs:[Clock] -> {ys:[Clock] | len xs == len ys} -> Bool @-}
vclLessEqualClocks :: [Clock] -> [Clock] -> Bool
vclLessEqualClocks (x:xs) (y:ys) = x <= y && vclLessEqualClocks xs ys
vclLessEqualClocks [] [] = True
vclLessEqualClocks _ _ = impossibleConst False "lists have same length"


-- * User API

-- |
--
-- >>> vclNew []
-- empty-vc
-- >>> vclNew [cafe, face]
-- 0000cafe-0000-cafe-0000-cafe0000cafe:t0
-- 0000face-0000-face-0000-face0000face:t0
--
{-@ inline vclNew @-}
vclNew :: [pid] -> VCL pid
vclNew pids = VCL pids $ listReplicate (listLength pids) 0

-- |
--
-- >>> vclRead beef $ vclNew [] -- this case eliminated by LH precondition
-- 0
-- >>> vclRead cafe $ vclNew [cafe]
-- 0
--
-- Recursive cases.
--
-- >>> vclRead beef (cafe # vclNew [cafe]) -- this case eliminated by LH precondition
-- 0
-- >>> vclRead face (cafe # face # vclNew [cafe, face])
-- 1
--
-- QuickCheck properties.
--
-- prop> 0 == vclRead pid (vclNew [])
-- prop> 1 == vclRead pid (pid # vclNew [pid])
--
{-@ inline vclRead @-}
{-@ vclRead :: p:pid -> {vc:VCL pid | vclHasPid p vc} -> Clock @-}
vclRead :: Eq pid => pid -> VCL pid -> Clock
vclRead pid (VCL pids clocks)
    = maybeFromJust 0 $ listGetIndex clocks (listElemIndex pid pids)

-- |
--
-- >>> cafe `vclTick` VCL [cafe] [1] -- update
-- 0000cafe-0000-cafe-0000-cafe0000cafe:t2
--
-- >>> cafe `vclTick` VCL [beef, cafe, face] [1, 1, 1]
-- 0000beef-0000-beef-0000-beef0000beef:t1
-- 0000cafe-0000-cafe-0000-cafe0000cafe:t2
-- 0000face-0000-face-0000-face0000face:t1
--
-- >>> beef # beef # cafe # vclNew [beef, cafe, face]
-- 0000beef-0000-beef-0000-beef0000beef:t2
-- 0000cafe-0000-cafe-0000-cafe0000cafe:t1
-- 0000face-0000-face-0000-face0000face:t0
-- >>> cafe # cafe # vclNew [beef, cafe, face]
-- 0000beef-0000-beef-0000-beef0000beef:t0
-- 0000cafe-0000-cafe-0000-cafe0000cafe:t2
-- 0000face-0000-face-0000-face0000face:t0
--
-- QuickCheck property showing that the result is the same regardless of the
-- order of ticks.
--
-- prop> vclTick a (vclTick b $ vclNew [a, b]) == vclTick b (vclTick a $ vclNew [a, b])
{-@ inline vclTick @-}
{-@ vclTick :: p:pid -> {vc:VCL pid | vclHasPid p vc} -> VCL pid @-}
vclTick :: Eq pid => pid -> VCL pid -> VCL pid
vclTick pid (VCL pids clocks) = VCL pids $ listSetIndex clocks (clock+1) index
  where
    index = listElemIndex pid pids
    clock = maybeFromJust 0 $ listGetIndex clocks index

-- |
--
-- >>> vclCombine (vclNew []) (vclNew [])
-- empty-vc
--
-- >>> vclCombine (cafe # vclNew [cafe]) (cafe # vclNew [cafe]) -- compare
-- 0000cafe-0000-cafe-0000-cafe0000cafe:t1
-- >>> vclCombine (cafe # cafe # vclNew [cafe]) (cafe # vclNew [cafe]) -- compare
-- 0000cafe-0000-cafe-0000-cafe0000cafe:t2
-- >>> vclCombine (cafe # vclNew [cafe]) (cafe # cafe # vclNew [cafe]) -- compare
-- 0000cafe-0000-cafe-0000-cafe0000cafe:t2
--
-- >>> vclCombine (beef # beef # cafe # vclNew [beef, cafe, face]) (cafe # cafe # vclNew [beef, cafe, face]) -- compare
-- 0000beef-0000-beef-0000-beef0000beef:t2
-- 0000cafe-0000-cafe-0000-cafe0000cafe:t2
-- 0000face-0000-face-0000-face0000face:t0
--
-- QuickCheck property for commutativity.
--
-- prop> let a = VCL pids aClocks; b = VCL pids bClocks in vclCombine a b == vclCombine b a
{-@ inline vclCombine @-}
{-@ vclCombine :: a:VCL pid -> {b:VCL pid | vclPidsMatch a b} -> {c:VCL pid | vclPidsMatch a c && vclPidsMatch b c} @-}
vclCombine :: VCL pid -> VCL pid -> VCL pid
vclCombine (VCL aPids aClocks) (VCL _ bClocks)
    = VCL aPids $ vclCombineClocks aClocks bClocks

-- |
--
-- >>> vclLessEqual (vclNew []) (vclNew []) -- nil-nil
-- True
--
-- >>> vclLessEqual (cafe # vclNew [cafe]) (cafe # vclNew [cafe]) -- compare
-- True
-- >>> vclLessEqual (cafe # cafe # vclNew [cafe]) (cafe # vclNew [cafe]) -- compare
-- False
-- >>> vclLessEqual (cafe # vclNew [cafe]) (cafe # cafe # vclNew [cafe]) -- compare
-- True
--
-- >>> vclLessEqual (beef # cafe # face # vclNew [beef, cafe, face]) (beef # cafe # face # vclNew [beef, cafe, face])
-- True
-- >>> vclLessEqual (beef # cafe # face # vclNew [beef, cafe, face]) (beef # face # vclNew [beef, cafe, face])
-- False
-- >>> vclLessEqual (beef # face # vclNew [beef, cafe, face]) (beef # cafe # face # vclNew [beef, cafe, face])
-- True
{-@ inline vclLessEqual @-}
{-@ vclLessEqual :: a:VCL pid -> {b:VCL pid | vclPidsMatch a b} -> Bool @-}
vclLessEqual :: VCL pid -> VCL pid -> Bool
vclLessEqual (VCL _ aClocks) (VCL _ bClocks)
    = vclLessEqualClocks aClocks bClocks

{-@ inline vclLess @-}
{-@ vclLess :: a:VCL pid -> {b:VCL pid | vclPidsMatch a b} -> Bool @-}
vclLess :: Eq pid => VCL pid -> VCL pid -> Bool
vclLess a b = vclLessEqual a b && a /= b

-- |
--
-- >>> vclIndependent (vclNew []) (vclNew [])
-- True
{-@ inline vclIndependent @-}
{-@ vclIndependent :: a:VCL pid -> {b:VCL pid | vclPidsMatch a b} -> Bool @-}
vclIndependent :: Eq pid => VCL pid -> VCL pid -> Bool
vclIndependent a b = not (vclLess a b) && not (vclLess b a)
