module Redefined.List where

import Language.Haskell.Liquid.ProofCombinators

import qualified Redefined.Fin () -- Required to prevent LH matchTyCon error
import Redefined.Bool

-- $setup
-- >>> :set -XFlexibleInstances
-- >>> instance Show (a -> b) where show _ = "(a -> b)"
-- >>> import Data.List

-- | Reify the @len@ measure defined in the @liquid-base@ specification into
-- code and back into specifications.
--
-- prop> length xs == listLength xs
{-@ measure listLength @-}
{-@ listLength :: xs:_ -> {v:Nat | v == len xs } @-}
listLength :: [a] -> Int
listLength [] = 0
listLength (_x:xs) = 1 + listLength xs

-- | Implementation of 'replicate' lifted to specifications. Probably same as
-- that of 'Prelude'.
--
-- prop> replicate n x == listReplicate n x
{-@ reflect listReplicate @-}
{-@ listReplicate :: n:Nat -> item:a -> {xs:[{x:a | x == item}] | n == listLength xs} @-}
listReplicate :: Int -> a -> [a]
listReplicate n x
    | n <= 0    = []
    | otherwise = x:listReplicate (n-1) x

-- | Implementation of 'map' lifted to specifications. Probably same as
-- 'Prelude'.
--
-- prop> map f xs == listMap f xs
{-@ reflect listMap @-}
{-@ listMap :: _ -> ps:[a] -> {qs:[b] | listLength ps == listLength qs} @-}
listMap :: (a -> b) -> [a] -> [b]
listMap f (x:xs) = f x:listMap f xs
listMap _ [] = []

{-@ ple listMap2 @-} -- To know that the argument to the function is a member of the list.
{-@ reflect listMap2 @-}
{-@ listMap2 :: ps:[a] -> ({x:a | listElem x ps} -> b) -> {qs:[b] | listLength ps == listLength qs} @-}
listMap2 :: [a] -> (a -> b) -> [b]
listMap2 (x:xs) f = f x:listMap2 xs f
listMap2 [] _ = []

-- | Implementation of 'foldr' lifted to specifications. Probably same as
-- 'Prelude'.
--
-- prop> foldr f acc xs == listFoldr f acc xs
{-@ reflect listFoldr @-}
listFoldr :: (a -> b -> b) -> b -> [a] -> b
listFoldr f acc (x:xs) = f x (listFoldr f acc xs)
listFoldr _ acc [] = acc

-- | Implementation of 'and' lifted to specifications. Probably same as
-- 'Prelude'.
--
-- prop> and xs == listAnd xs
{-@ reflect listAnd @-} -- FIXME: this causes a crash when it's a measure?
listAnd :: [Bool] -> Bool
listAnd = listFoldr boolAnd True

-- | Implementation of 'or' lifted to specifications. Probably same as
-- 'Prelude'.
--
-- prop> or xs == listOr xs
{-@ reflect listOr @-} -- FIXME: this causes a crash when it's a measure?
listOr :: [Bool] -> Bool
listOr = listFoldr boolOr False

-- | Implementation of 'reverse' lifted to specifications. Copied from
-- 'Prelude'.
--
-- prop> reverse xs == listReverse xs
{-@ inline listReverse @-}
{-@ listReverse :: xs:_ -> {ys:_ | listLength xs == listLength ys} @-}
listReverse :: [a] -> [a]
listReverse orig = listReverseImpl orig []

{-@ reflect listReverseImpl @-}
{-@ listReverseImpl :: xs:_ -> ys:_ -> {zs:_ | listLength xs + listLength ys == listLength zs} @-}
listReverseImpl :: [a] -> [a] -> [a]
listReverseImpl []     done = done
listReverseImpl (x:xs) done = listReverseImpl xs (x:done)

-- | Similar to @base:Data.List.elemIndex@ or
-- @containers:Data.Sequence.elemeIndexL@, "elemIndexL finds the leftmost index
-- of the specified element, if it is present, and otherwise Nothing," but is
-- implemented more simply.
--
-- prop> elemIndex a xs == listElemIndex a xs
{-@ inline listElemIndex @-}
{-@ listElemIndex :: x:_ -> xs:_ -> {m:_ | listElem x xs => isJust m} @-}
listElemIndex :: Eq a => a -> [a] -> Maybe Int
listElemIndex a xs = listElemIndexImpl a xs 0

{-@ reflect listElemIndexImpl @-}
{-@ listElemIndexImpl :: x:_ -> xs:_ -> _ -> {m:_ | listElem x xs => isJust m} @-}
{-@ ple listElemIndexImpl @-}
listElemIndexImpl :: Eq a => a -> [a] -> Int -> Maybe Int
listElemIndexImpl _ [] _ = Nothing
listElemIndexImpl a (x:xs) idx
    | a == x = Just idx
    | otherwise = listElemIndexImpl a xs (idx + 1)

-- | Implementation of 'elem' lifted to specifications. Copied from 'Prelude'.
--
-- prop> elem a xs == listElem a xs
{-@ reflect listElem @-}
listElem :: Eq a => a -> [a] -> Bool
listElem _ []     = False
listElem x (y:ys) = x==y || listElem x ys

-- | Implementation of 'init' combined with 'last' lifted to specifications.
--
-- prop> not (null xs) ==> (init xs, last xs) == listInitLast xs
{-@ reflect listInitLast @-}
{-@ listInitLast :: {xs:[a] | 0 < len xs} -> ([a], a) @-}
listInitLast :: [a] -> ([a], a)
listInitLast [x] = ([], x)
listInitLast (a:b:cs) = let (xs, x) = listInitLast (b:cs) in (a:xs, x)

-- | Lookup an element of a non-empty list given a valid index. This is called
-- "lookup" in agda and "!!" or "genericIndex" in haskell.
--
-- prop> 0 <= i && i < length xs ==> xs !! i == listIndex xs i
{-@ reflect listIndex @-}
{-@ listIndex :: xs:[a] -> Fin {len xs} -> a @-}
listIndex :: [a] -> Int -> a
listIndex (x:xs) i
    | i == 0    = x
    | otherwise = listIndex xs (i-1)

-- | Implementation of 'filter' lifted to specifications. Implemented with
-- foldr; no idea if this matches what's in 'Prelude'.
--
-- prop> filter p xs == listFilter p xs
{-@ reflect listFilter @-}
listFilter :: (a -> Bool) -> [a] -> [a]
listFilter p = listFoldr (listFilterImpl p) []

{-@ reflect listFilterImpl @-}
listFilterImpl :: (a -> Bool) -> a -> [a] -> [a]
listFilterImpl p x xs = if p x then x:xs else xs

-- | Implementation of 'zip' lifted to specifications. Copied from 'Prelude'.
--
-- prop> zip xs ys == listZip xs ys
{-@ reflect listZip @-}
listZip :: [a] -> [b] -> [(a, b)]
listZip [] _ = []
listZip _ [] = []
listZip (a:as) (b:bs) = (a, b) : listZip as bs

-- | Implementation of 'zipWith' lifted to specifications. Copied from
-- 'Prelude'.
--
-- prop> zipWith f xs ys == listZipWith f xs ys
{-@ reflect listZipWith @-}
listZipWith :: (a -> b -> c) -> [a] -> [b] -> [c]
listZipWith _ [] _ = []
listZipWith _ _ [] = []
listZipWith f (x:xs) (y:ys) = f x y : listZipWith f xs ys

-- | Implementation of 'zipWith3' lifted to specifications. Copied from
-- 'zipWith'.
--
-- prop> zipWith3 f xs ys zs == listZipWith3 f xs ys zs
{-@ reflect listZipWith3 @-}
listZipWith3 :: (a -> b -> c -> d) -> [a] -> [b] -> [c] -> [d]
listZipWith3 _ [] _ _ = []
listZipWith3 _ _ [] _ = []
listZipWith3 _ _ _ [] = []
listZipWith3 f (x:xs) (y:ys) (z:zs) = f x y z : listZipWith3 f xs ys zs

-- | Implementation of 'splitAt' lifted to specifications. Copied from
-- 'Prelude'.
--
-- prop> splitAt i xs == listSplitAt i xs
{-@ reflect listSplitAt @-}
listSplitAt :: Int -> [a] -> ([a], [a])
listSplitAt n xs | n <= 0 = ([], xs)
listSplitAt _ [] = ([], [])
listSplitAt 1 (x:xs) = ([x], xs)
listSplitAt n (x:xs) = (x:ys, zs)
  where
    (ys, zs) = listSplitAt (n - 1) xs

-- * Racket things reimplemented

{-@ reflect listAndMap @-}
listAndMap :: (a -> Bool) -> [a] -> Bool
listAndMap f xs = listAnd (listMap f xs)

{-@ reflect listOrMap @-}
listOrMap :: (a -> Bool) -> [a] -> Bool
listOrMap f xs = listOr (listMap f xs)

-- * Other things

-- | Does the first list appear as a tail-sublist of the second list? The case
-- where two equal lists are provided returns false.
--
-- >>> "foo" `listIsTailOf` "foo"
-- False
-- >>> "foo" `listIsTailOf` "bar"
-- False
-- >>> "hell" `listIsTailOf` "hello"
-- False
-- >>> "lo" `listIsTailOf` "hello"
-- True
--
-- prop> a `listIsTailOf` a == False
{-@ reflect listIsTailOf @-}
listIsTailOf :: Eq a => [a] -> [a] -> Bool
listIsTailOf _smaller [] = False
listIsTailOf smaller (_b:bigger) = smaller == bigger || smaller `listIsTailOf` bigger

{-@ reflect listTailForHead @-}
--- {-@ ple listTailForHead @-} -- To show `listElem t (x:xs) && t /= x => listElem t xs`
--- {-@ listTailForHead :: t:a -> {xs:[a] | listElem t xs} -> [a] @-}
listTailForHead :: Eq a => a -> [a] -> [a]
listTailForHead _target [] = []
listTailForHead target (x:xs) = if target == x then xs else listTailForHead target xs

-- * Examples, proofs, and properties

-- | A list is [] if and only if its length is zero.
--
{-@ ple listEmptyIffLengthZero @-}
{-@ reflect listEmptyIffLengthZero @-}
{-@ listEmptyIffLengthZero :: xs:[a] -> { [] == xs <=> 0 == listLength xs } @-}
listEmptyIffLengthZero :: [a] -> Proof
listEmptyIffLengthZero [] = ()
listEmptyIffLengthZero (_:_) = ()

-- | The head of a strictly-ascending list does not appear in the tail.
--
{-@ ple ordListHeadNotInTail @-}
{-@ reflect ordListHeadNotInTail @-}
{-@ ordListHeadNotInTail :: {xs:[a]<{\x y -> x < y}> | 0 < listLength xs} -> { not (listElem (head xs) (tail xs)) } @-}
ordListHeadNotInTail :: [a] -> Proof
ordListHeadNotInTail (_x:[]) = () -- x is not in empty list
ordListHeadNotInTail (_x:_y:[]) = () -- x is not y
ordListHeadNotInTail (x:_y:zs) = ordListHeadNotInTail (x:zs) -- x is not y and <inductive hypothesis>

-- {-@ ple ordListHeadLessThanTail @-}
-- {-@ ordListHeadLessThanTail :: {xs:[a]<{\x y -> x < y}> | 0 < listLength xs} -> { listOrMap ((head xs) <) (tail xs) } @-}
-- ordListHeadLessThanTail :: [a] -> Proof
-- ordListHeadLessThanTail _ = ()
