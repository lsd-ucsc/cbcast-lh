module Redefined.Set where

import Language.Haskell.Liquid.ProofCombinators

import Redefined.Proof
import Redefined.List

-- $setup
-- >>> import Data.Set

data Set a = Set [a] deriving Eq
{-@ data Set [setSize] a = Set [a]<{\x y -> x < y}> @-}

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

-- set_ex1 :: Set Char
-- set_ex1 = Set ('a':'b':[])
-- FIXME

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

{-@ ple setUnionCommutative @-}
{-@
setUnionCommutative
    :: xs:Set a
    -> ys:Set a
    -> { setUnion xs ys == setUnion ys xs }
    / [setSize xs + setSize ys]
@-}
setUnionCommutative :: Ord a => Set a -> Set a -> Proof
setUnionCommutative (Set []) (Set []) = ()
setUnionCommutative xs (Set []) = ()
--  = setUnion xs (Set []) === xs === setUnion (Set []) xs *** QED
setUnionCommutative (Set []) ys = ()
--  = setUnion (Set []) ys === ys === setUnion ys (Set []) *** QED
setUnionCommutative (Set (x:xs)) (Set (y:ys))
    | x < y = setUnionCommutative (Set xs) (Set (y:ys))
--      = setUnion (Set (x:xs)) (Set (y:ys))
--      === (let Set zs = setUnion (Set xs) (Set (y:ys)) in Set (x:zs))
--      === Set (x:(let Set zs = setUnion (Set xs) (Set (y:ys)) in zs))
--          ? setUnionCommutative (Set xs) (Set (y:ys))
--      === Set (x:(let Set zs = setUnion (Set (y:ys)) (Set xs) in zs))
--      *** QED
    | y < x = setUnionCommutative (Set (x:xs)) (Set ys)
--      =   setUnion (Set (x:xs)) (Set (y:ys))
--      === (let Set zs = setUnion (Set (x:xs)) (Set ys) in Set (y:zs))
--      === Set (y:(let Set zs = setUnion (Set (x:xs)) (Set ys) in zs))
--          ? setUnionCommutative (Set (x:xs)) (Set ys)
--      === Set (y:(let Set zs = setUnion (Set ys) (Set (x:xs)) in zs))
--      *** QED

    | otherwise
        =   () *** Admit
--      =   setUnion (Set (x:xs)) (Set (y:ys))
--          ? (True === x == y)
--      === setUnion (Set xs) (Set (y:ys))
--          ? setUnionCommutative (Set xs) (Set (y:ys))
--      === setUnion (Set (y:ys)) (Set xs)
--      *** Admit

--  | otherwise = case xs of
--      []
--          ->  setUnion (Set (x:xs)) (Set (y:ys))
--          === setUnion (Set xs) (Set (y:ys))
--          === setUnion (Set []) (Set (y:ys))
--              ? setUnionCommutative (Set []) (Set (y:ys))
--          === setUnion (Set (y:ys)) (Set [])
--          *** Admit
--      (b:bs)
--          -> undefined
--          ->  setUnion (Set (x:xs)) (Set (y:ys))
--          === setUnion (Set xs) (Set (y:ys))
--              ? setUnionCommutative (Set xs) (Set (y:ys))
--          === Set (y:(let Set zs = setUnion (Set xs) (Set ys) in zs))
--              ? setUnionCommutative (Set xs) (Set ys)
--          === Set (y:(let Set zs = setUnion (Set ys) (Set xs) in zs))
--          === Set (x:(let Set zs = setUnion (Set ys) (Set xs) in zs))
--          === (let Set zs = setUnion (Set ys) (Set xs) in Set (x:zs))
--          === setUnion (Set (x:ys)) (Set xs)
--          === setUnion (Set (y:ys)) (Set xs)
--          *** Admit

-- {-@ ple setUnionMembership @-}
-- {-@
-- setUnionMembership
--     ::    q:a
--     ->   xs:Set a
--     ->   ys:Set a
--     -> { setMember q xs || setMember q ys
--             => setMember q (setUnion xs ys) }
-- @-}
-- setUnionMembership :: Ord a => a -> Set a -> Set a -> Proof
-- setUnionMembership q xs (Set []) = ()
-- setUnionMembership q (Set []) ys = ()
-- setUnionMembership q (Set (x:xs)) (Set (y:ys))
--     | setMember q (Set (x:xs)) = () *** Admit
--     | setMember q (Set (y:ys)) =
--         ()
--             ? setUnionCommutative (Set (x:xs)) (Set (y:ys))
--             ? setUnionMembership q (Set (ys)) (Set (xs))
--         *** Admit
--     | otherwise = ()

--  | x < y
--      =   
--      (   setMember q (setUnion (Set (x:xs)) (Set (y:ys)))
--      === setMember q (let Set zs = setUnion (Set xs) (Set (y:ys)) in Set (x:zs))
--      === listElem q (let Set zs = setUnion (Set xs) (Set (y:ys)) in x:zs)
--      === listElem q (x:(let Set zs = setUnion (Set xs) (Set (y:ys)) in zs))
--      === (q==x || listElem q (let Set zs = setUnion (Set xs) (Set (y:ys)) in zs))
--      === (q==x || setMember q (setUnion (Set xs) (Set (y:ys))))
--      *** QED
--      )
--      &&&
--      (   if q==x
--      then () *** QED
--      else setUnionMembership q (Set xs) (Set (y:ys))
--      )
--  | y < x = () *** Admit
--  | otherwise = () *** Admit

----  =   setMember q (setUnion (Set (x:xs)) (Set (y:ys)))
----  === 
----  -- () ? setMemberUnionLeft q (Set xs) (Set ys)
----  *** Admit
