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

-- | A fully reversible swap of domain and range.
{-@ reflect swapDomainRange @-}
-- {-@ swapDomainRange :: ab:BinaryRelation a b -> {ba:BinaryRelation b a | ab == swapDomainRange ba} @-}
-- {-@ swapDomainRange :: ab:BinaryRelation a b -> {ba:BinaryRelation b a | setSize ab == setSize ba} @-}
swapDomainRange :: (Ord a, Ord b) => BinaryRelation a b -> BinaryRelation b a
swapDomainRange = setFromList . listMap tupleSwap . setAscList

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
swapPreservesMember (a, b) (Set (x@(a', b'):xs))
    =   setMember (tupleSwap (a, b)) (swapDomainRange (Set (x:xs)))
    === setMember (b, a) (setFromList (listMap tupleSwap (x:xs)))
    === setMember (b, a) (setFromList (tupleSwap x : listMap tupleSwap xs))
    === setMember (b, a) (Set [tupleSwap x] `setUnion` setFromList (listMap tupleSwap xs))
        ? setMemberDistributesOverUnion (b, a) (Set [tupleSwap x]) (setFromList (listMap tupleSwap xs))
    === ( setMember (b, a) (Set [tupleSwap x]) || setMember (b, a) (setFromList (listMap tupleSwap xs)) )
    === ( setMember (b, a) (Set [tupleSwap x]) || setMember (b, a) (swapDomainRange (Set xs)) )
        ? swapPreservesMember (a, b) (Set xs)
    === ( setMember (b, a) (Set [tupleSwap x]) || setMember (a, b) (Set xs) )
    === ( listElem (b, a) [tupleSwap x] || setMember (a, b) (Set xs) )
    === ( (b, a) == (tupleSwap x) || setMember (a, b) (Set xs) )
    === ( (b, a) == (tupleSwap (a', b')) || setMember (a, b) (Set xs) )
    === ( (b, a) == (b', a') || setMember (a, b) (Set xs) )
    === ( (a, b) == (a', b') || setMember (a, b) (Set xs) )
    *** QED
    *** Admit

-- * Tuples

{-@ reflect firstEquals @-}
firstEquals :: Eq a => a -> (a, b) -> Bool
firstEquals a' (a, _b) = a' == a

{-@ reflect secondEquals @-}
secondEquals :: Eq b => b -> (a, b) -> Bool
secondEquals b' (_a, b) = b' == b
