-- | Implementation of vector clocks over polymorphic PIDs using a pair of a
-- PID list and a Clock list constrained to have the same lengths.
--
-- Functions operating on pairs of VCs constrain those to have the same list of
-- PIDs.
module Causal.VCLite
( module Causal.VCLite
, module Redefined
) where

import Data.UUID (UUID)
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

data VCL pid = VCL [pid] [Clock] deriving Eq
{-@
data VCL pid = VCL
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
    = VCL aPids $ vclCombineImpl aClocks bClocks
{-@ reflect vclCombineImpl @-}
{-@ vclCombineImpl :: xs:[Clock] -> {ys:[Clock] | len xs == len ys} -> {zs:[Clock] | len xs == len zs && len ys == len zs} @-}
vclCombineImpl :: [Clock] -> [Clock] -> [Clock]
vclCombineImpl (x:xs) (y:ys) = (if x < y then y else x):vclCombineImpl xs ys
vclCombineImpl [] [] = []
vclCombineImpl _ _ = impossibleConst [] "lists have same length"

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
    = vclLessEqualImpl aClocks bClocks
{-@ reflect vclLessEqualImpl @-}
{-@ vclLessEqualImpl :: xs:[Clock] -> {ys:[Clock] | len xs == len ys} -> Bool @-}
vclLessEqualImpl :: [Clock] -> [Clock] -> Bool
vclLessEqualImpl (x:xs) (y:ys) = x <= y && vclLessEqualImpl xs ys
vclLessEqualImpl [] [] = True
vclLessEqualImpl _ _ = impossibleConst False "lists have same length"

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

-- | Determine message deliverability relative to current vector time.
--
--      "(2) On reception of message m sent by p_i and timestamped with VT(m),
--      process p_j =/= p_i delays delivery of m until:
--
--          for-all k: 1...n { VT(m)[k] == VT(p_j)[k] + 1 if k == i
--                           { VT(m)[k] <= VT(p_j)[k]     otherwise"
--
-- @vclDeliverable mSender mSent localTime@ computes whether a message sent by
-- @mSender@ at @mSent@ is deliverable at @localTime@.
--
{-@ inline vclDeliverable @-}
{-@ vclDeliverable :: mSender:pid -> {mSent:VCL pid | vclHasPid mSender mSent} -> {localTime:VCL pid | vclHasPid mSender localTime && vclPidsMatch mSent localTime} -> Bool @-}
vclDeliverable :: Eq pid => pid -> VCL pid -> VCL pid -> Bool
vclDeliverable mSender (VCL _ mClocks) (VCL pPids pClocks)
    = vclDeliverableImpl mSender mClocks pPids pClocks
{-@ vclDeliverableImpl :: pid -> ws:[Clock] -> {xs:[pid] | len ws == len xs} -> {ys:[Clock] | len ws == len ys && len xs == len ys} -> Bool @-}
{-@ reflect vclDeliverableImpl @-}
vclDeliverableImpl :: Eq pid => pid -> [Clock] -> [pid] -> [Clock] -> Bool
vclDeliverableImpl mSender (mClock:mRest) (pid:pids) (pClock:pRest)
    | pid == mSender    = mClock == pClock + 1 && vclDeliverableImpl mSender mRest pids pRest
    | pid /= mSender    = mClock <= pClock     && vclDeliverableImpl mSender mRest pids pRest
vclDeliverableImpl _ [] [] [] = True
vclDeliverableImpl _ _ _ _ = impossibleConst False "lists have same length"


-- * Wrapper

type PID = UUID
-- | Wrapper around "VCL" with PIDs anchored to UUID. LH has trouble reflecting
-- functions that have UUID in the type, but if we hide it inside a data
-- constructor, it works.
{-@
data VC = VC (VCL PID) @-}
data VC = VC (VCL PID) deriving Eq

{-@ inline vcHasPid @-}
vcHasPid :: UUID -> VC -> Bool
vcHasPid pid (VC x) = vclHasPid pid x

{-@ inline vcPidsMatch @-}
vcPidsMatch :: VC -> VC -> Bool
vcPidsMatch (VC a) (VC b) = vclPidsMatch a b

{-@ inline vcNew @-}
vcNew :: [UUID] -> VC
vcNew pids = VC $ vclNew pids

{-@ inline vcRead @-}
{-@ vcRead :: p:UUID -> {vc:VC | vcHasPid p vc} -> Clock @-}
vcRead :: UUID -> VC -> Clock
vcRead pid (VC x) = vclRead pid x

{-@ inline vcTick @-}
{-@ vcTick :: p:UUID -> {vc:VC | vcHasPid p vc} -> VC @-}
vcTick :: UUID -> VC -> VC
vcTick pid (VC x) = VC (vclTick pid x)

{-@ inline vcCombine @-}
{-@ vcCombine :: a:VC -> {b:VC | vcPidsMatch a b} -> {c:VC | vcPidsMatch a c && vcPidsMatch b c} @-}
vcCombine :: VC -> VC -> VC
vcCombine (VC a) (VC b) = VC (vclCombine a b)

{-@ inline vcLessEqual @-}
{-@ vcLessEqual :: a:VC -> {b:VC | vcPidsMatch a b} -> Bool @-}
vcLessEqual :: VC -> VC -> Bool
vcLessEqual (VC a) (VC b) = vclLessEqual a b

{-@ inline vcLess @-}
{-@ vcLess :: a:VC -> {b:VC | vcPidsMatch a b} -> Bool @-}
vcLess :: VC -> VC -> Bool
vcLess (VC a) (VC b) = vclLess a b

-- | @vcDeliverable mSender mSent localTime@ computes whether a message sent by
-- @mSender@ at @mSent@ is deliverable at @localTime@.
{-@ inline vcDeliverable @-}
{-@ vcDeliverable :: mSender:UUID -> {mSent:VC | vcHasPid mSender mSent} -> {localTime:VC | vcHasPid mSender localTime && vcPidsMatch mSent localTime} -> Bool @-}
vcDeliverable :: PID -> VC -> VC -> Bool
vcDeliverable mSender (VC mSent) (VC localTime) = vclDeliverable mSender mSent localTime
