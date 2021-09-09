module Data.BinaryRelation where

import Language.Haskell.Liquid.ProofCombinators

import Redefined.Tuple
import Redefined.List
import Redefined.Set

type BinaryRelation a b = Set (a, b)

{-@ reflect brEmpty @-}
brEmpty :: BinaryRelation a b
brEmpty = setEmpty

{-@ reflect brDomain @-}
brDomain :: Ord a => BinaryRelation a b -> Set a
brDomain = setFromList . listMap tupleFirst . setAscList

{-@ reflect brRange @-}
brRange :: Ord b => BinaryRelation a b -> Set b
brRange = setFromList . listMap tupleSecond . setAscList

{-@ reflect brRangeFor @-}
-- | Analogue to calling a function, except that a relation may associate a set
-- of values with some input.
brRangeFor :: (Eq a, Ord b) => a -> BinaryRelation a b -> Set b
brRangeFor a = setFromList . listMap tupleSecond . listFilter (firstEquals a) . setAscList
--TODO implement with setMap(?) and setFilter

{-@ reflect brDomainFor @-}
-- | Like running a function backwards to get the set of inputs which
-- correspond to an output.
brDomainFor :: (Eq b, Ord a) => b -> BinaryRelation a b -> Set a
brDomainFor b = setFromList . listMap tupleFirst . listFilter (secondEquals b) . setAscList
--TODO implement with setMap(?) and setFilter

{-@ reflect brWithRange @-}
-- | Use a value as the domain for an existing range.
brWithRange :: (Ord a, Ord b) => a -> Set b -> BinaryRelation a b
brWithRange a = setFromList . listMap ((,) a) . setAscList
---TODO withRange :: a -> x:Set b -> {y:Relation a b | setSize x == setSize y} @-}

---- -- | Given (a,b), for every (b,c) in the relation add an (a,c) to the result.
---- --
---- -- a -> b -> c
---- --
---- -- >>> brTransitive $ Set [(1,2),(2,3)]
---- -- {(1,2),(1,3),(2,3)}
---- --
---- -- !!! a -> b -> c
---- -- !!!        `-> c'
---- --
---- -- !!! >>> brTransitive $ Set [(1,2),(2,3),(2,999)]
---- -- !!! {(1,2),(1,3),(1,999),(2,3),(2,999)}
---- --
---- -- a -> b -> c -> d
---- --
---- -- >>> brTransitive $ Set [(1,2),(2,3),(3,4)]
---- -- {(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)}
---- --
---- {-@ reflect brTransitive @-}
---- {-@ brTransitive :: br:BinaryRelation a a -> BinaryRelation a a / [setSize br] @-}
---- brTransitive :: Eq a => BinaryRelation a a -> BinaryRelation a a
---- brTransitive (Set []) = Set []
---- brTransitive (Set ((a,b):rest)) =
----     let Set done = brTransitivitySweep (a,b) (brTransitive (Set rest))
----     in Set ((a,b):done)

---- -- | Given (b,c), for every (a,b) in the relation add an (a,c) to the result.
---- --
---- -- >>> brTransitivitySweep (2,3) (Set [(1,2)])
---- -- {(1,2),(2,3)}
---- --
---- -- >>> brTransitivitySweep (2,3) $ Set [(2,999)]
---- -- {(2,999)}
---- --
---- -- >>> brTransitivitySweep (1,2) $ Set [(2,999)]
---- -- {(1,999),(2,999)}
---- --
---- -- >>> brTransitivitySweep (1,2) $ Set [(2,3),(2,999)]
---- -- {(1,3),(2,3),(1,999),(2,999)}
---- --
---- {-@ reflect brTransitivitySweep @-}
---- brTransitivitySweep :: Eq a => BinaryRelation a a -> (a, a) -> BinaryRelation a a
---- brTransitivitySweep (Set []) _ = Set []
---- brTransitivitySweep (Set ((a,b):rest)) (b',c)
----     | b == b'   = let Set done = brTransitivitySweep (Set rest) (b',c) in Set ((a,b):(a,c):done)
----     | otherwise = let Set done = brTransitivitySweep (Set rest) (b',c) in Set ((a,b):      done)
---- 
---- -- | Given (a,b), for every (b,c) in the relation add an (a,c) to the result.
---- --
---- -- >>> brTransitivitySweepOld (1,2) (Set [(2,3)])
---- -- {(1,3),(2,3)}
---- --
---- -- >>> brTransitivitySweepOld (2,3) $ Set [(2,999)]
---- -- {(2,999)}
---- --
---- -- >>> brTransitivitySweepOld (1,2) $ Set [(2,999)]
---- -- {(1,999),(2,999)}
---- --
---- -- >>> brTransitivitySweepOld (1,2) $ Set [(2,3),(2,999)]
---- -- {(1,3),(2,3),(1,999),(2,999)}
---- --
---- {-@ reflect brTransitivitySweepOld @-}
---- {-@ brTransitivitySweepOld :: (a, a) -> br:BinaryRelation a a -> BinaryRelation a a / [setSize br] @-}
---- brTransitivitySweepOld :: Eq a => (a, a) -> BinaryRelation a a -> BinaryRelation a a
---- brTransitivitySweepOld _ (Set []) = Set []
---- brTransitivitySweepOld (a,b) (Set ((b',c):rest))
----     | b == b'   = let Set done = brTransitivitySweepOld (a,b) (Set rest) in Set ((a,c):(b',c):done)
----     | otherwise = let Set done = brTransitivitySweepOld (a,b) (Set rest) in Set (      (b',c):done)

--burabura :: (a, a) -> BinaryRelation a a -> BinaryRelation a a
--burabura (a,b) (Set br) = Set ((a,b):br)
--
--burabura_ :: (a, a) -> Set (a,a) -> Set (a,a)
--burabura_ (a,b) (Set br) = Set ((a,b):br)

---- -- TODO: state this property more generally? like, can we state transitivity as
---- -- a property of a relation and then prove that the result of brTransitive
---- -- satisfies it?
---- {-@
---- brTransitiveTransitivity
----     ::   br:BinaryRelation a a
----     ->   x:a
----     -> { y:a | setMember (x,y)   br }
----     -> { z:a | setMember   (y,z) br }
----     -> {       setMember (x,  z) (brTransitive br) }
----     /  [setSize br]
---- @-}
---- {-@ ple brTransitiveTransitivity @-}
---- brTransitiveTransitivity :: Eq a => BinaryRelation a a -> a -> a -> a -> Proof
---- brTransitiveTransitivity (Set []) _x _y _z = ()
---- brTransitiveTransitivity (Set ((a,b):rest)) x y z
----     | setMember (x,z) (brTransitive (Set ((a,b):rest))) = ()
----     | otherwise
----         =   False
----         === setMember (x,z) (brTransitive (Set ((a,b):rest)))
----         === setMember (x,z) (let Set done = brTransitivitySweep (a,b) (brTransitive (Set rest)) in Set ((a,b):done))
----         === setMember (x,z) (Set ((a,b) : (let Set done = brTransitivitySweep (a,b) (brTransitive (Set rest)) in done)))
----         === listElem (x,z) ((a,b) : (let Set done = brTransitivitySweep (a,b) (brTransitive (Set rest)) in done))
----         === 
----         *** Admit


---- {-@
---- type Transitive
----     =  br:BinaryRelation a a
----     -> x:a
----     -> y:a
----     -> z:a
----     -> { setMember (x,y) br && setMember (y,z) br => setMember (x,z) br }
---- @-}
---- 
---- {-@
---- makeTransitiveWorks ::

