module Causal.VCLite where

import Redefined (listLength, listElem, impossibleConst)

-- $setup
-- >>> import Data.List (elemIndex)
-- >>> import Data.Maybe (fromMaybe)
-- >>> import Data.Typeable (Typeable(..), typeOf)
-- >>> instance (Typeable a, Typeable b) => Show (a -> b) where show = show . typeOf


-- * Types

type Clock = Integer
{-@ type Clock = {c:Integer | cMin <= c} @-}

data VC pid
    = VC [pid] [Clock]
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
-- >>> larger 1 2
-- 2
-- >>> larger 2 1
-- 2
{-@ inline larger @-}
larger :: Ord a => a -> a -> a
larger a b = if a < b then b else a

{-@ inline vcHasPid @-}
vcHasPid :: Eq pid => pid -> VC pid -> Bool
vcHasPid pid (VC pids _) = listElem pid pids

{-@ inline vcPidsMatch @-}
vcPidsMatch :: Eq pid => VC pid -> VC pid -> Bool
vcPidsMatch (VC aPids _) (VC bPids _) = aPids == bPids


-- * User API

{-@ inline vcNewImpl @-}
vcNewImpl :: [pid] -> VC pid
vcNewImpl pids = VC pids $ listReplicate (listLength pids) 0

{-@ inline vcRead @-}
{-@ vcRead :: p:pid -> {vc:VC pid | vcHasPid p vc} -> Clock @-}
vcRead :: Eq pid => pid -> VC pid -> Clock
vcRead pid (VC pids clocks) = maybeFromJust 0 $ listGetIndex clocks (listElemIndex pid pids)

{-@ inline vcTick @-}
{-@ vcTick :: p:pid -> {vc:VC pid | vcHasPid p vc} -> VC pid @-}
vcTick :: Eq pid => pid -> VC pid -> VC pid
vcTick pid (VC pids clocks) = VC pids $ listSetIndex clocks (clock+1) index
  where
    index = listElemIndex pid pids
    clock = maybeFromJust 0 $ listGetIndex clocks index

-- {-@ inline vcCombine1 @-} -- FIXME can't lift a partially applied function to specifications
{-@ vcCombine1 :: a:VC pid -> {b:VC pid | vcPidsMatch a b} -> {c:VC pid | vcPidsMatch a c && vcPidsMatch b c} @-}
vcCombine1 :: Eq pid => VC pid -> VC pid -> VC pid
vcCombine1 (VC aPids aClocks) (VC bPids bClocks)
    | aPids == bPids    = VC aPids $ listZipWith larger aClocks bClocks
    | otherwise         = impossibleConst (VC [] []) "vcPidsMatch a b"

-- {-@ inline vcCombine2 @-} -- FIXME can't lift a partially applied function to specifications
{-@ vcCombine2 :: a:VC pid -> {b:VC pid | vcPidsMatch a b} -> {c:VC pid | vcPidsMatch a c && vcPidsMatch b c} @-}
vcCombine2 :: Eq pid => VC pid -> VC pid -> VC pid
vcCombine2 (VC aPids aClocks) (VC _ bClocks)
    = VC aPids $ listZipWith larger aClocks bClocks

{-@ inline vcCombine @-}
{-@ vcCombine :: a:VC pid -> {b:VC pid | vcPidsMatch a b} -> {c:VC pid | vcPidsMatch a c && vcPidsMatch b c} @-}
vcCombine :: Eq pid => VC pid -> VC pid -> VC pid
vcCombine (VC aPids aClocks) (VC _ bClocks)
    = VC aPids $ vcCombineClocks aClocks bClocks

{-@ reflect vcCombineClocks @-}
{-@ vcCombineClocks :: xs:[Clock] -> {ys:[Clock] | len xs == len ys} -> {zs:[Clock] | len xs == len zs && len ys == len zs} @-}
vcCombineClocks :: [Clock] -> [Clock] -> [Clock]
vcCombineClocks (x:xs) (y:ys) = (if x < y then y else x):vcCombineClocks xs ys
vcCombineClocks [] [] = []
vcCombineClocks _ _ = impossibleConst [] "lists have same length"
