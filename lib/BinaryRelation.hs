module BinaryRelation where

import Redefined

type BinaryRelation a b = Set (a, b)

{-@ reflect domain @-}
domain :: Ord a => BinaryRelation a b -> Set a
domain = setFromList . listMap tupleFirst . setAscList

{-@ reflect range @-}
range :: Ord b => BinaryRelation a b -> Set b
range = setFromList . listMap tupleSecond . setAscList

{-@ reflect rangeFor @-}
-- | Analogue to calling a function, except that a relation can return a set of
-- values for an input.
rangeFor :: (Eq a, Ord b) => a -> BinaryRelation a b -> Set b
rangeFor a = setFromList . listMap tupleSecond . listFilter (firstEquals a) . setAscList
--TODO implement with setMap(?) and setFilter

{-@ reflect domainFor @-}
-- | Like running a function backwards to get the set of inputs which
-- correspond to an output.
domainFor :: (Eq b, Ord a) => b -> BinaryRelation a b -> Set a
domainFor b = setFromList . listMap tupleFirst . listFilter (secondEquals b) . setAscList
--TODO implement with setMap(?) and setFilter

{-@ reflect withRange @-}
-- | Use a value as the domain for an existing range.
withRange :: (Ord a, Ord b) => a -> Set b -> BinaryRelation a b
withRange a = setFromList . listMap ((,) a) . setAscList
---TODO withRange :: a -> x:Set b -> {y:Relation a b | setSize x == setSize y} @-}

-- * Tuples

{-@ reflect firstEquals @-}
firstEquals :: Eq a => a -> (a, b) -> Bool
firstEquals a' (a, _b) = a' == a

{-@ reflect secondEquals @-}
secondEquals :: Eq b => b -> (a, b) -> Bool
secondEquals b' (_a, b) = b' == b
