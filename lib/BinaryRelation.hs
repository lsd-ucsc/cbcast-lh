module BinaryRelation where

import Redefined
import Language.Haskell.Liquid.ProofCombinators

type BinaryRelation a b = Set (a, b)

{-@ reflect domain @-}
domain :: Ord a => BinaryRelation a b -> Set a
domain = setFromList . listMap tupleFirst . setAscList

{-@ reflect range @-}
range :: Ord b => BinaryRelation a b -> Set b
range = setFromList . listMap tupleSecond . setAscList

{-@ reflect rangeFor @-}
-- | Analogue to calling a function, except that a relation may associate a set
-- of values with some input.
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

-- | A fully reversible swap of domain and range.
{-@ reflect swapDomainRange @-}
swapDomainRange :: (Ord a, Ord b) => BinaryRelation a b -> BinaryRelation b a
swapDomainRange = setFromList . listMap tupleSwap . setAscList
-- {-@ swapDomainRange :: ab:BinaryRelation a b -> {ba:BinaryRelation b a | ab == swapDomainRange ba} @-}
-- {-@ swapDomainRange :: ab:BinaryRelation a b -> {ba:BinaryRelation b a | setSize ab == setSize ba} @-}

{-@ ple setMemberDistributesOverUnion @-}
{-@ setMemberDistributesOverUnion :: z:a -> xs:Set a -> ys:Set a
        -> { setMember z (setUnion xs ys) <=> setMember z xs || setMember z ys }
        / [setSize xs + setSize ys]
@-}
setMemberDistributesOverUnion :: Ord a => a -> Set a -> Set a -> Proof
setMemberDistributesOverUnion _ _ (Set []) = () -- Base case for setUnion
setMemberDistributesOverUnion _ (Set []) _ = () -- Base case for setUnion
setMemberDistributesOverUnion z (Set (x:xs)) (Set (y:ys)) -- Inductive hypothesises for setUnion recursive cases
    | x < y = setMemberDistributesOverUnion z (Set xs) (Set (y:ys))
    | y < x = setMemberDistributesOverUnion z (Set (x:xs)) (Set ys)
    | otherwise = setMemberDistributesOverUnion z (Set xs) (Set (y:ys))

{-@ ple swapPreservesMember @-}
{-@ swapPreservesMember :: t:(a, b) -> r:BinaryRelation a b
        -> { setMember t r <=> setMember (tupleSwap t) (swapDomainRange r) }
        / [setSize r]
@-}
swapPreservesMember :: (Ord a, Ord b) => (a, b) -> BinaryRelation a b -> Proof
swapPreservesMember _ (Set []) = () -- Base case for setMember
swapPreservesMember (a, b) (Set ((a', b'):xs))
    = ()
        ? setMemberDistributesOverUnion (b, a) (Set [tupleSwap (a', b')]) (setFromList (listMap tupleSwap xs))
        ? swapPreservesMember (a, b) (Set xs)

{-@ ple swapPreservesRelation @-}
{-@ swapPreservesRelation :: r:BinaryRelation a b
        -> { r == swapDomainRange (swapDomainRange r) }
        / [setSize r]
@-}
swapPreservesRelation :: (Ord a, Ord b) => BinaryRelation a b -> Proof
swapPreservesRelation (Set []) = ()
swapPreservesRelation (Set ((a, b):xs))
    =   swapDomainRange (swapDomainRange (Set ((a, b):xs)))
    === swapDomainRange (setFromList (listMap tupleSwap ((a, b):xs)))
    === swapDomainRange (setFromList (tupleSwap (a, b) : listMap tupleSwap xs))
    === swapDomainRange (setSingleton (tupleSwap (a, b)) `setUnion` setFromList (listMap tupleSwap xs))
--      ? swapDistributesOverUnion
    *** Admit
---- swapPreservesRelation (Set (x:xs))
----  =   setMember  swapPreservesMember x (Set xs)
----  *** Admit

{-@ ple swapDistributesOverUnion @-}
{-@ swapDistributesOverUnion :: xs:BinaryRelation a b -> ys:BinaryRelation a b
        -> { setUnion (swapDomainRange xs) (swapDomainRange ys) == swapDomainRange (setUnion xs ys) }
@-}
swapDistributesOverUnion :: BinaryRelation a b -> BinaryRelation a b -> Proof
swapDistributesOverUnion _ _ = () *** Admit

-- * Tuples

{-@ reflect firstEquals @-}
firstEquals :: Eq a => a -> (a, b) -> Bool
firstEquals a' (a, _b) = a' == a

{-@ reflect secondEquals @-}
secondEquals :: Eq b => b -> (a, b) -> Bool
secondEquals b' (_a, b) = b' == b
