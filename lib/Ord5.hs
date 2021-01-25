{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE LambdaCase #-}
module Ord5 where

import Language.Haskell.Liquid.ProofCombinators (Proof, trivial, (===), (***), QED(..))

--- {-@ type OAssocLB  k v LB = [{tup:(     k            , v) | LB < fst tup}]<{\a b -> fst a < fst b}> @-}
--- {-@ type OAssocLB2 k v LB = [     ({key:k | LB < key}, v)                ]<{\a b -> fst a < fst b}> @-}
--- 
--- -- {-@ x :: OAssocLB Int Char 0 @-}
--- -- x :: [(Int, Char)]
--- -- x = (1,'z'):(2,'b'):[]
--- -- 
--- -- {-@ x2 :: OAssocLB2 Int Char 0 @-}
--- -- x2 :: [(Int, Char)]
--- -- x2 = (1,'z'):(2,'b'):[]
--- 
--- {-@
--- ins :: lb:k -> ({newK:k | lb < newK}, v) -> OAssocLB k v lb -> OAssocLB k v lb @-}
--- ins :: (Ord k, Semigroup v) => k -> (k, v) -> [(k, v)] -> [(k, v)]
--- ins _ (newK, newV) assoc = case assoc of
---     [] -> [(newK, newV)]
---     (curK, curV) : rest
---         | newK <  curK -> (newK, newV) : (curK, curV) : rest
---         | newK == curK -> (curK, newV <> curV) : rest
---         | otherwise    -> (curK, curV) : ins curK (newK, newV) rest
--- 
--- {-@
--- ins2 :: lb:k -> ({newK:k| lb < newK} , v) -> OAssocLB2 k v lb -> OAssocLB2 k v lb @-}
--- {-@ ignore ins2 @-}
--- ins2 :: (Ord k, Semigroup v) => k -> (k, v) -> [(k, v)] -> [(k, v)]
--- ins2 _ (newK, newV) assoc = case assoc of
---     [] -> [(newK, newV)]
---     (curK, curV) : rest
---         | newK <  curK -> (newK, newV) : (curK, curV) : rest
---         | newK == curK -> (curK, newV <> curV) : rest
---         | otherwise    -> (curK, curV) : ins2 curK (newK, newV) rest
--- 
--- ----

data Foo = Foo Int Int deriving (Eq, Ord)
{-@
data Foo = Foo
    { ffst ::    Int
    , fsnd :: {v:Int | v /= 0}
    }
@-}

lessEqItem :: (Foo, v) -> (Foo, v) -> Bool
lessEqItem (i, _) (j, _) = lessEq i j
{-@ inline lessEqItem @-}

lessEq :: Foo -> Foo -> Bool
lessEq (Foo x y) (Foo a b) = x <= a && div x y <= div a b
-- lessEq a b = a <= b
{-@ inline lessEq @-}

type           FooAssoc v = [   (Foo, v)                   ]
{-@ type      FooOAssoc v = [   (Foo, v)                   ]<{\a b -> lessEqItem a b}> @-}
{-@ type FooOAssocLB v LB = [{p:(Foo, v) | lessEqItem LB p}]<{\a b -> lessEqItem a b}> @-}

-- {-@
-- insertAheadFieldsLB :: lb:(Foo, v) -> {p:(Foo, v) | lessEqItem lb p} -> FooOAssocLB v lb -> FooOAssocLB v lb @-}
insertAheadFieldsLB :: (Foo, v) -> (Foo, v) -> FooAssoc v -> FooAssoc v
insertAheadFieldsLB lb new = \case
    [] -> new:[]
    cur:rest
        | new `lessEqItem` cur -> new:cur:rest
--      | cur `lessEqItem` 
        | otherwise                -> cur:insertAheadFieldsLB new new rest

{-@ ltP :: a:Foo -> b:Foo -> {a < b => not (b < a)} @-}
ltP :: Foo -> Foo -> Proof
ltP _ _ = trivial

{-@ leP :: a:Foo -> b:Foo -> {a <= b && a /= b => not (b <= a)} @-}
leP :: Foo -> Foo -> Proof
leP _ _ = trivial

-- {-@ lessEqP :: a:Foo -> b:Foo -> {lessEq a b && a /= b => not (lessEq b a)} @-}
-- lessEqP :: Foo -> Foo -> Proof
-- --lessEqP _ _ = trivial
-- lessEqP i@(Foo x y) j@(Foo a b)
--     =   (lessEq i j                   && i /= j)
--     === (x <= a && div x y <= div a b && (x /= a || y /= b))
--     *** Admit
-- {-@ ple lessEqP @-}




-- {-@ ignore insertAheadUnpacking @-}
-- {-@
-- insertAheadUnpacking :: (Foo, v) -> FooOAssoc v -> FooOAssoc v @-}
-- insertAheadUnpacking :: (Foo, v) -> FooAssoc v -> FooAssoc v
-- insertAheadUnpacking new@(newK, _) = \case
--     [] -> new:[]
--     cur@(curK, _):rest
--         | newK `lessEq` curK -> new:cur:rest
--         | otherwise          -> cur:insertAheadUnpacking new rest
-- 
-- {-@ ignore insertAheadFields @-}
-- {-@
-- insertAheadFields :: (Foo, v) -> FooOAssoc v -> FooOAssoc v @-}
-- insertAheadFields :: (Foo, v) -> FooAssoc v -> FooAssoc v
-- insertAheadFields new = \case
--     [] -> new:[]
--     cur:rest
--         | fst new `lessEq` fst cur -> new:cur:rest
--         | otherwise                -> cur:insertAheadFields new rest
