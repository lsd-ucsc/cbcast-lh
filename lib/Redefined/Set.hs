module Redefined.Set where

import Language.Haskell.Liquid.ProofCombinators

import Redefined.Proof
import Redefined.List

-- $setup
-- >>> import Data.Set

data Set a = Set [a] deriving Eq
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
{-@ setAscList :: ps:Set a -> {qs:[a] | setSize ps == listLength qs} @-}
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

-- | Proof helper for deconstructing a set.
--
{-@ ple setUncons @-}
{-@ reflect setUncons @-}
{-@ setUncons :: {s:Set a | 0 < setSize s} -> (a, Set a)<{\x xs -> not (setMember x xs) }> @-}
setUncons :: Set a -> (a, Set a)
setUncons (Set (x:xs)) = (x, Set xs) `proofConst` ordListHeadNotInTail (x:xs)

-- * Examples, proofs, and properties

set_ex1 :: Set Char
set_ex1 = Set ('a':'b':[])

{-@ fail set_ex2 @-}
set_ex2 :: Set Char
set_ex2 = Set ('b':'a':[])

{-@ set_propMembersAreAscending :: {s:Set a | 2 == setSize s} -> {b:Bool | b <=> True} @-}
set_propMembersAreAscending :: Ord a => Set a -> Bool
set_propMembersAreAscending (Set (a:b:[])) = a < b

{-@ set_propHeadNotInTail :: {s:Set a | 0 < setSize s} -> {b:Bool | b <=> True} @-}
set_propHeadNotInTail :: Ord a => Set a -> Bool
set_propHeadNotInTail (Set (x:xs)) = not (x `listElem` xs) ? ordListHeadNotInTail (x:xs)

{-@ ple set_propHeadNotInTail2 @-}
{-@ set_propHeadNotInTail2 :: {s:Set a | 0 < setSize s} -> {b:Bool | b <=> True} @-}
set_propHeadNotInTail2 :: Ord a => Set a -> Bool
set_propHeadNotInTail2 (Set (x:xs)) = not (x `setMember` Set xs) ? ordListHeadNotInTail (x:xs)

{-@ ple setEmptyIffSizedZero @-}
{-@ setEmptyIffSizedZero :: s:Set a -> { setEmpty == s <=> 0 == setSize s } @-}
setEmptyIffSizedZero :: Set a -> Proof
setEmptyIffSizedZero (Set xs) = () `proofConst` listEmptyIffLengthZero xs

-- {-@ setUnionUndoesUncons :: {s:Set a | 0 < setSize s} -> (a, Set a)<{\x xs -> s == setUnion (setSingleton x) xs }> @-}
-- setUnionUndoesUncons :: Set a -> Proof
-- setUnionUndoesUncons _ = ()

{-@ ple setIntensionalGivesExtensional @-}
{-@ setIntensionalGivesExtensional :: xs:Set a -> ys:Set a
        -> { z:a | setMember z xs <=> setMember z ys }
        -> { xs == ys }
@-}
setIntensionalGivesExtensional :: Eq a => Set a -> Set a -> a -> Proof
setIntensionalGivesExtensional _ _ _ = () *** Admit
--  | (Set []) == ys = ()
--  | (Set []) /= ys
--      =   ys
--          ? (setMember z ys === False)
--      === (Set [])

--- setIntensionalIffExtensional _ (Set []) _
---     = () *** Admit
--- setIntensionalIffExtensional (Set (x:xs)) (Set (y:ys)) z
---     = () *** Admit
--- 
--- --- {-@ ple setWithoutMembersEmpty @-}
--- --- {-@ setWithoutMembersEmpty :: xs:Set a -> {z:a | not (setMember z xs)} -> { xs == Set [] } @-}
--- --- setWithoutMembersEmpty :: Set a -> a -> Proof
--- --- setWithoutMembersEmpty (Set []) z = () -- easy
--- --- setWithoutMembersEmpty (Set (x:xs)) z = setMember x (Set (x:xs))
--- 
--- 
--- {-@ blah :: xs:Set a -> (z:a -> { not (setMember z xs) }) -> { xs == Set [] } @-}
--- blah :: Eq a => Set a -> (a -> Proof) -> Proof
--- blah (Set []) f = ()
--- blah (Set (x:xs)) f
---     = () *** Admit
--- --  =   setMember x (Set (x:xs))
--- --  === True
--- --      ? f x
--- --  *** QED ---  ? blah (Set xs) f
--- 
--- -- {-@ consedMemberIsMember :: x:a -> xs:[a]<{\a b -> x < a && a < b}> -> { setMember x (Set (x:xs)) } @-}
--- -- consedMemberIsMember :: a -> [a] -> Proof
--- -- consedMemberIsMember _ _ = () *** Admit
--- 
--- 
--- 
--- 
--- 
--- 
--- 
--- 
--- 
--- 
--- 
--- 
--- 
--- 
