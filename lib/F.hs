module F where

import qualified Data.Set as S -- Lifted: Set, empty, singleton, member, union, intersection, difference

import Language.Haskell.Liquid.Equational (eq)
import Language.Haskell.Liquid.ProofCombinators (Proof, (===), (***))
import qualified Language.Haskell.Liquid.ProofCombinators as Proof

-- TWO MORE IDEAS
--  * rewrite "sorted" to get rid of the tuples; extract the list of keys and then guarantee it's sorted
--  * try to write this "Assoc k v" merge over an explicit data structure with three fields

type Assoc k v = [(k, v)]
{-@ type Assoc k v      = [   (k, v)              ]<{\a b -> fst a < fst b}> @-}
{-@ type AssocLB k v LB = [{t:(k, v) | LB < fst t}]<{\a b -> fst a < fst b}> @-}

{-@ ok :: Assoc Char Int @-}
ok :: Assoc Char Int
ok = [('a', 1), ('b', 1), ('c', 1)]

{-@ ignore bad @-}
{-@ bad :: Assoc Char Int @-}
bad :: Assoc Char Int
bad = [('a', 1), ('b', 1), ('a', 1)]

{-@ measure keys @-}
keys :: Ord k => Assoc k v -> S.Set k
keys [] = S.empty
keys ((k,_):xs) = S.singleton k `S.union` keys xs

-- | This describes the condition necessary to `cons` to `Assoc`.
--
{-@ cons :: lb:k -> v -> AssocLB k v lb -> Assoc k v @-}
cons :: k -> v -> Assoc k v -> Assoc k v
cons k v xs = (k,v):xs

-- | This should describe the property preserved through `merge` which allows
-- consing to the result.
--
-- {-@
-- mergeP :: lb:k -> f:(v -> v -> v) -> xs:AssocLB k v lb -> ys:AssocLB k v lb
--     -> { merge f xs ys }
-- @-}
mergeP :: k -> Assoc k v -> Assoc k v -> Proof
mergeP _ _ _
    =   ()
    *** Proof.Admit

-- {-@ merge :: _ -> xs:Assoc k v -> ys:Assoc k v -> {zs:Assoc k v | S.union (keys xs) (keys ys) == keys zs} @-}
-- {-@ merge :: _ -> xs:Assoc k v -> ys:Assoc k v -> zs:Assoc k v @-}
merge :: Ord k => (v -> v -> v) -> Assoc k v -> Assoc k v -> Assoc k v
merge _ a [] = a
merge _ [] b = b
merge f as@(a@(ak,av):as') bs@(b@(bk,bv):bs')
--  | ak == bk  = (ak,f av bv):merge f as' bs'
--  | ak <  bk  = a:merge f as' bs
--  | otherwise = b:merge f as  bs'
    | otherwise = []
