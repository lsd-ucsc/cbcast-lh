module Data.BinaryRelation where

import Language.Haskell.Liquid.ProofCombinators

import Redefined.Function
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
brRangeFor :: (Eq a, Ord b) => BinaryRelation a b -> a -> Set b
brRangeFor br a = setFromList . listMap tupleSecond . listFilter (firstEquals a) . setAscList $ br
--TODO implement with setMap(?) and setFilter

{-@ reflect brDomainFor @-}
-- | Like running a function backwards to get the set of inputs which
-- correspond to an output.
brDomainFor :: (Eq b, Ord a) => BinaryRelation a b -> b -> Set a
brDomainFor br b = setFromList . listMap tupleFirst . listFilter (secondEquals b) . setAscList $ br
--TODO implement with setMap(?) and setFilter

{-@ reflect brWithRange @-}
-- | Use a value as the domain for an existing range.
brWithRange :: (Ord a, Ord b) => a -> Set b -> BinaryRelation a b
brWithRange a bs = setFromList . listMap ((,) a) . setAscList $ bs
---TODO withRange :: a -> x:Set b -> {y:Relation a b | setSize x == setSize y} @-}

{-@ reflect brWithDomain @-}
-- | Use a value as the range for an existing domain.
brWithDomain :: (Ord a, Ord b) => Set a -> b -> BinaryRelation a b
brWithDomain as b = setFromList . listMap (funFlip (,) b) . setAscList $ as


-- | Make a relation transitive.
--
-- 1 -> 2 -> 3
-- add 1->3
--
-- >>> brTransitive $ Set [(1,2),(2,3)]
-- {(1,2),(1,3),(2,3)}
--
-- 1 -> 2 -> 3
--       `-> 4
-- add 1->3
-- add 1->4
--
-- >>> brTransitive $ Set [(1,2),(2,3),(2,999)]
-- {(1,2),(1,3),(1,999),(2,3),(2,999)}
--
-- 1 -> 2 -> 3 -> 4
-- add 1->3
-- add 1->4
-- add 2->4
--
-- >>> brTransitive $ Set [(1,2),(2,3),(3,4)]
-- {(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)}
--
-- TODO: abitrary instance for Set
-- !!! prop> setMember (a,b) br && setMember (b,c) br ===> setMember (a,c) (brTransitive br)
--
{-@ reflect brTransitive @-}
{-@ brTransitive :: br:BinaryRelation a a -> BinaryRelation a a / [setSize br] @-}
brTransitive :: Ord a => BinaryRelation a a -> BinaryRelation a a
brTransitive (Set []) = Set []
brTransitive (Set ((a,b):rest)) =
    setSingleton (a,b) `setUnion` brTransitiveHelper (a,b) (brTransitive (Set rest))

-- | Given (a,b), for every (x,y) in the relation if b==x add (a,y) to the
-- result or if y==a add (x,b) to the result. This is a helper function for
-- making a relation transitive, and otherwise shouldn't be used.
--
-- >>> brTransitiveHelper (1,2) (Set [(2,3)])
-- {(1,3),(2,3)}
--
-- >>> brTransitiveHelper (2,3) $ Set [(2,999)]
-- {(2,999)}
--
-- >>> brTransitiveHelper (1,2) $ Set [(2,999)]
-- {(1,999),(2,999)}
--
-- >>> brTransitiveHelper (1,2) $ Set [(2,3),(2,999)]
-- {(1,3),(1,999),(2,3),(2,999)}
--
{-@ reflect brTransitiveHelper @-}
{-@
brTransitiveHelper
    :: (a, a)
    -> BinaryRelation a a
    -> BinaryRelation a a
@-}
brTransitiveHelper :: Ord a => (a, a) -> BinaryRelation a a -> BinaryRelation a a
brTransitiveHelper _ (Set []) = Set []
brTransitiveHelper (a,b) (Set ((x,y):rest))
    | b == x    = done `setUnion` setSingleton (a,y) -- a->b, x->y, b==x implies a->y
    | y == a    = done `setUnion` setSingleton (x,b) -- x->y, a->b, y==a implies x->b
    | otherwise = done
  where
    done = setSingleton (x,y) `setUnion` brTransitiveHelper (a,b) (Set rest)

{-@ ple brTransitiveHelperTransitivity @-}
{-@
brTransitiveHelperTransitivity
    ::  br:BinaryRelation t t
    ->   a:t
    ->   b:t
    -> { c:t | setMember (b,c) br }
    -> {       setMember (a,c) (brTransitiveHelper (a,b) br) }
@-}
brTransitiveHelperTransitivity :: Eq t => BinaryRelation t t -> t -> t -> t -> Proof
brTransitiveHelperTransitivity (Set []) _a _b _c = ()
brTransitiveHelperTransitivity br@(Set ((x,y):rest)) a b c = () *** Admit

-- TODO: state this property more generally? like, can we state transitivity as
-- a property of a relation and then prove that the result of brTransitive
-- satisfies it?
{-@ ple brTransitiveTransitivity @-}
{-@
brTransitiveTransitivity
    ::  br:BinaryRelation t t
    ->   a:t
    -> { b:t | setMember (a,b) br }
    -> { c:t | setMember (b,c) br }
    -> {       setMember (a,c) (brTransitive br) }
@-}
brTransitiveTransitivity :: Eq t => BinaryRelation t t -> t -> t -> t -> Proof
brTransitiveTransitivity (Set []) _a _b _c = ()
brTransitiveTransitivity br@(Set ((x,y):rest)) a b c
--  | (a,b) == (x,y) = () *** Admit
--  | (b,c) == (x,y) = () *** Admit
--  | otherwise = () ? brTransitiveTransitivity (Set rest) a b c
    = () *** Admit

--  if setMember (a,b) (Set rest) && setMember (b,c) (Set rest)
--  then () ? brTransitiveTransitivity (Set rest) a b c
--  else () *** Admit -- The premises don't hold for rest
--  | setMember (x,z) (brTransitive (Set ((a,b):rest))) = ()
--  | otherwise
--      =   False
--      === setMember (x,z) (brTransitive (Set ((a,b):rest)))
--      === setMember (x,z) (let Set done = brTransitiveHelper (a,b) (brTransitive (Set rest)) in Set ((a,b):done))
--      === setMember (x,z) (Set ((a,b) : (let Set done = brTransitiveHelper (a,b) (brTransitive (Set rest)) in done)))
--      === listElem (x,z) ((a,b) : (let Set done = brTransitiveHelper (a,b) (brTransitive (Set rest)) in done))
--      === 
--      *** Admit

---- -- | Make a relation transitive.
---- --
---- -- a -> b -> c
---- --
---- -- >>> brTransitive $ Set [(1,2),(2,3)]
---- -- {(1,2),(1,3),(2,3)}
---- --
---- -- a -> b -> c
---- --        `-> c'
---- --
---- -- >>> brTransitive $ Set [(1,2),(2,3),(2,999)]
---- -- {(1,2),(1,3),(1,999),(2,3),(2,999)}
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
----     let Set done = brTransitiveHelper (a,b) (brTransitive (Set rest))
----     in Set ((a,b):done)

----- -- head of a set is a lower bound for rest
----- 
----- {-@ type BinaryRelationLB a b LB = Set { brlbP:(a, b) | LB < brlbP } @-}
----- 
----- {-@ ple brTransitive @-}
----- {-@ reflect brTransitive @-}
----- brTransitive :: Eq a => BinaryRelation a a -> BinaryRelation a a
----- brTransitive (Set []) = Set []
----- brTransitive (Set ((a,b):rest)) =
-----     let Set done = brTransitiveHelper (a,b) (brTransitive (Set rest)
-----             `proofConst` brTransitivePreservesLowerBound (a,b) (Set rest
-----                     `proofConst` brHeadIsLowerBoundForTail (a,b) rest (Set ((a,b):rest))))
-----     in Set ((a,b):done)
----- 
----- {-@
----- brTransitivePreservesLowerBound
-----     ::   lb:(a,a)
-----     -> { br:BinaryRelation a a | isLowerBound lb br }
-----     -> { isLowerBound lb (brTransitive br) } @-}
----- brTransitivePreservesLowerBound :: (a, a) -> BinaryRelation a a -> Proof
----- brTransitivePreservesLowerBound _ _ = () *** Admit -- show that brTransitive doesn't change the lower bound
----- 
----- {-@ reflect listCons @-}
----- listCons :: a -> [a] -> [a]
----- listCons x xs = x:xs
----- 
----- {-@
----- brHeadIsLowerBoundForTail
-----     ::  hd:a
-----     ->  tl:[a]
-----     -> { s:Set a | s == Set (listCons hd tl) }
-----     -> { isLowerBound hd (Set tl) }
----- @-}
----- brHeadIsLowerBoundForTail :: a -> [a] -> Set a -> Proof
----- brHeadIsLowerBoundForTail _x _xs _s = () *** Admit
----- 
----- -- | Given (a,b), for every (x,y) in the relation if b==x add (a,y) to the
----- -- result or if y==a add (x,b) to the result.
----- --
----- -- >>> brTransitiveHelper (1,2) (Set [(2,3)])
----- -- {(1,3),(2,3)}
----- --
----- -- >>> brTransitiveHelper (2,3) $ Set [(2,999)]
----- -- {(2,999)}
----- --
----- -- >>> brTransitiveHelper (1,2) $ Set [(2,999)]
----- -- {(1,999),(2,999)}
----- --
----- -- >>> brTransitiveHelper (1,2) $ Set [(2,3),(2,999)]
----- -- {(1,3),(2,3),(1,999),(2,999)}
----- --
----- {-@ reflect brTransitiveHelper @-}
----- {-@
----- brTransitiveHelper
-----     ::  p:(a, a)
-----     -> br:BinaryRelationLB a a {p}
-----     ->    BinaryRelationLB a a {p}
-----     / [setSize br]
----- @-}
----- brTransitiveHelper :: Eq a => (a, a) -> BinaryRelation a a -> BinaryRelation a a
----- brTransitiveHelper _ (Set []) = Set []
----- brTransitiveHelper (a,b) (Set ((x,y):rest))
-----     | b == x    = Set ((a,y):(x,y):done) -- a->b, x->y, b==x implies a->y
-----     | y == a    = Set ((x,b):(x,y):done) -- x->y, a->b, y==a implies x->b
-----     | otherwise = Set (      (x,y):done)
-----   where
-----     Set done = brTransitiveHelper (a,b) (Set rest)
----- -- TODO: how to state "forall x. setMember x inp => setMember x out"

------- -- | Given (a,b), for every (x,y) in the relation if b==x add (a,y) to the
------- -- result or if y==a add (x,b) to the result.
------- --
------- -- >>> brTransitiveHelper (1,2) (Set [(2,3)])
------- -- {(1,3),(2,3)}
------- --
------- -- >>> brTransitiveHelper (2,3) $ Set [(2,999)]
------- -- {(2,999)}
------- --
------- -- >>> brTransitiveHelper (1,2) $ Set [(2,999)]
------- -- {(1,999),(2,999)}
------- --
------- -- >>> brTransitiveHelper (1,2) $ Set [(2,3),(2,999)]
------- -- {(1,3),(2,3),(1,999),(2,999)}
------- --
------- {-@ reflect brTransitiveHelper @-}
------- {-@
------- brTransitiveHelper
-------     :: (a, a)
-------     -> BinaryRelation a a
-------     -> BinaryRelation a a
------- @-}
------- brTransitiveHelper :: Eq a => (a, a) -> BinaryRelation a a -> BinaryRelation a a
------- brTransitiveHelper _ (Set []) = Set []
------- brTransitiveHelper (a,b) (Set ((x,y):rest))
-------     | b == x    = Set ((a,y):(x,y):done) -- a->b, x->y, b==x implies a->y
-------     | y == a    = Set ((x,b):(x,y):done) -- x->y, a->b, y==a implies x->b
-------     | otherwise = Set (      (x,y):done)
-------   where
-------     Set done = brTransitiveHelper (a,b) (Set rest)
-------         `proofConst` brTransitivitySweepPreservesLowerBound (a,b) (Set ((x,y):rest))
------- 
------- {-@ reflect isLowerBound @-}
------- isLowerBound :: Ord a => a -> Set a -> Bool
------- isLowerBound _lb (Set []) = True
------- isLowerBound lb (Set (x:xs)) = lb < x && isLowerBound lb (Set xs)
------- 
------- {-@
------- brTransitivitySweepPreservesLowerBound
-------     ::   lb:(a,a)
-------     -> { br:BinaryRelation a a | isLowerBound lb br }
-------     -> { isLowerBound lb (brTransitiveHelper lb br) } @-}
------- brTransitivitySweepPreservesLowerBound :: (a, a) -> BinaryRelation a a -> Proof
------- brTransitivitySweepPreservesLowerBound _ _ = () *** Admit


--- type Transitive
---     =  br:BinaryRelation a a
---     -> x:a
---     -> y:a
---     -> z:a
---     -> { setMember (x,y) br && setMember (y,z) br => setMember (x,z) br }
--- 
--- type TransitiveRelation a = { r:BinaryRelation a a | checkTransitivity r }
