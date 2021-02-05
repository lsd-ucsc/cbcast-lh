-- | This module defines vector clocks using an association list of process ids
-- mapped to clock values.
--
-- Among the other attempts and implementations of vector clocks in this repo,
-- this one is the VectorClockRefl implementation. It uses a uniqueness measure
-- defined this way:
-- <https://ucsd-progsys.github.io/liquidhaskell-tutorial/Tutorial_08_Measure_Set.html>.
module Causal.VectorClock where

-- import Language.Haskell.Liquid.ProofCombinators (Proof, (===), (***))
-- import qualified Language.Haskell.Liquid.ProofCombinators as Proof

import qualified Data.Set as S -- Lifted: Set, empty, singleton, member, union, intersection, difference


-- * Haskell types

type Clock = Integer
type VCList pid = [(pid, Clock)]


-- * Logical predicates

-- | Return the set of PIDs in a vector clock.
vclPids :: Ord pid => VCList pid -> S.Set pid
vclPids vcl = case vcl of
    [] -> S.empty
    (pid,_):rest -> S.singleton pid `S.union` vclPids rest
{-@ measure vclPids @-}

-- | Are the PIDs in a vector clock unique?
vclPidsUnique :: Ord pid => VCList pid -> Bool
vclPidsUnique vcl = case vcl of
    [] -> True
    (pid,_):rest -> not (S.member pid $ vclPids rest) && vclPidsUnique rest
{-@ measure vclPidsUnique @-}


-- * LiquidHaskell types

{-@ type Clock = {c:Integer | 0 <= c} @-}
{-@ type RealClock = {c:Integer | 1 <= c} @-}
{-@ type VCList pid = {vcl:[(pid, RealClock)] | vclPidsUnique vcl} @-}


-- * User API

{-@ vclNew :: VCList pid @-}
vclNew :: VCList pid
vclNew = []

{-@ vclTick :: p:pid -> xs:VCList pid -> {ys:VCList pid | S.union (S.singleton p) (vclPids xs) == vclPids ys} @-}
vclTick :: Eq pid => pid -> VCList pid -> VCList pid
vclTick pid vcl = case vcl of
    []                  -> (pid,1):[]
    (cur,clock):rest
        | pid == cur    -> (cur,clock+1):rest
        | otherwise     -> (cur,clock):vclTick pid rest
