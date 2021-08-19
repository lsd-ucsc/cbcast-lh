module Redefined.Set where

import Redefined.List

-- $setup
-- >>> import Data.Set

data Set a = Set [a]
{-@ data Set a = Set [a]<{\x y -> x < y}> @-}

instance Show a => Show (Set a) where
    show (Set []) = "{}"
    show (Set xs) = ('{' :) . (++ "}") . tail . init . show $ xs

{-@ measure setSize @-}
{-@ setSize :: Set a -> Nat @-}
setSize :: Set a -> Int
setSize (Set xs) = listLength xs

-- |
--
-- >>> setEmpty
-- {}
{-@ reflect setEmpty @-}
setEmpty :: Set a
setEmpty = Set []

-- |
--
-- >>> setSingleton 'a'
-- {a}
-- >>> setSingleton 3
-- {3}
{-@ reflect setSingleton @-}
setSingleton :: a -> Set a
setSingleton x = Set [x]

-- |
--
-- prop> toAscList (fromList xs `union` fromList ys) == setAscList (setFromList xs `setUnion` setFromList ys)
{-@ setUnion :: xs:Set a -> ys:Set a -> Set a / [setSize xs + setSize ys] @-}
{-@ reflect setUnion @-}
setUnion :: Ord a => Set a -> Set a -> Set a
setUnion xs (Set []) = xs
setUnion (Set []) ys = ys
setUnion (Set (x:xs)) (Set (y:ys))
    | x < y = let Set zs = setUnion (Set    xs ) (Set (y:ys)) in Set (x:zs)
    | y < x = let Set zs = setUnion (Set (x:xs)) (Set    ys ) in Set (y:zs)
    | otherwise = setUnion (Set    xs ) (Set (y:ys))

-- |
--
-- >>> setFromList "hello"
-- {ehlo}
-- >>> setFromList [9, 3, 0, 9, 1, 1, 3, 1, 3, 0]
-- {0,1,3,9}
{-@ reflect setFromList @-}
setFromList :: Ord a => [a] -> Set a
setFromList [] = setEmpty
setFromList (x:xs) = setSingleton x `setUnion` setFromList xs

{-@ reflect setAscList @-}
setAscList :: Set a -> [a]
setAscList (Set xs) = xs

-- |
--
-- prop> member a (fromList xs) == setMember a (setFromList xs)
{-@ reflect setMember @-}
setMember :: Eq a => a -> Set a -> Bool
setMember el = listElem el . setAscList

-- |
--
-- prop> toAscList (delete a (fromList xs)) == setAscList (setDelete a (setFromList xs))
{-@ setDelete :: el:a -> xs:Set a -> ys:Set a / [setSize xs] @-}
-- XXX refine result to:
-- * one smaller if xs contained el
-- * ys doesn't contain el
{-@ reflect setDelete @-}
setDelete :: Ord a => a -> Set a -> Set a
setDelete _ (Set []) = setEmpty
setDelete el (Set (x:xs))
    | el == x = Set xs
    | otherwise = let ys = setDelete el (Set xs) in setSingleton x `setUnion` ys

-- | Subset checking implemented as O(n^2) membership check.
--
-- prop> isSubsetOf (fromList xs) (fromList ys) == setIsSubsetOf (setFromList xs) (setFromList ys)
{-@ reflect setIsSubsetOf @-}
setIsSubsetOf :: Eq a => Set a -> Set a -> Bool
setIsSubsetOf smaller bigger = listFoldr (setIsSubsetOfImpl bigger) True (setAscList smaller)

{-@ reflect setIsSubsetOfImpl @-}
setIsSubsetOfImpl :: Eq a => Set a -> a -> Bool -> Bool
setIsSubsetOfImpl bigger x ok = ok && setMember x bigger
