-- | This module defines vector clocks using an association list of process ids
-- mapped to clock values.
module Causal.VCList where

-- import Language.Haskell.Liquid.ProofCombinators (Proof, (===), (***))
-- import qualified Language.Haskell.Liquid.ProofCombinators as Proof

-- import qualified Data.Set as S -- Lifted: Set, empty, singleton, member, union, intersection, difference

import Assoc


-- * Types

type Clock = Integer
{-@ type     Clock = {c:Integer | 0 <= c} @-}
{-@ type RealClock = {c:Integer | 1 <= c} @-}

type VCList pid = Assoc pid Clock
{-@ type VCList pid = Assoc pid RealClock @-}

{-@ _ok :: VCList Char @-}
_ok :: VCList Char
_ok = ('a',1):('b',1):('c',1):[]

{-@ fail _badNotSorted @-}
{-@ _badNotSorted :: VCList Char @-}
_badNotSorted :: VCList Char
_badNotSorted = ('a',1):('b',1):('a',1):[]

{-@ fail _badNotRealClock @-}
{-@ _badNotRealClock :: VCList Char @-}
_badNotRealClock :: VCList Char
_badNotRealClock = ('a',1):('b',1):('c',0):[]


-- * Logical predicates

-- -- | Return the set of PIDs in a vector clock.
-- vclPids :: Ord pid => VCList pid -> S.Set pid
-- vclPids vcl = case vcl of
--     [] -> S.empty
--     (pid,_):rest -> S.singleton pid `S.union` vclPids rest
-- {-@ measure vclPids @-}
-- 
-- -- | Are the PIDs in a vector clock unique?
-- vclPidsUnique :: Ord pid => VCList pid -> Bool
-- vclPidsUnique vcl = case vcl of
--     [] -> True
--     (pid,_):rest -> not (S.member pid $ vclPids rest) && vclPidsUnique rest
-- {-@ measure vclPidsUnique @-}


-- * User API

{-@ vclEmpty :: VCList pid @-}
vclEmpty :: VCList pid
vclEmpty = []

{-@ vclTick :: pid -> VCList pid -> VCList pid @-}
vclTick :: Ord pid => pid -> VCList pid -> VCList pid
vclTick pid vcl =
--  let r = merge add [(pid,1)] vcl
--  in if valuesSatisfy (1<=) r then r else undefined
    merge add [(pid,1)] vcl
    `withProof`
    proofValuePredMaintained realClock add [(pid,1)] vcl

realClock :: Clock -> Bool
realClock c = 1 <= c
{-@ inline realClock @-}

-- -- {-@
-- -- proofRealClockPreservedByTick
-- --     :: p:pid
-- --     -> vc:VCList pid
-- --     -> {}
-- -- @-}
-- 
-- 
-- -- * Internals

{-@ add :: RealClock -> RealClock -> RealClock @-}
add :: Clock -> Clock -> Clock
add a b = a + b

-- {-@ max :: RealClock -> RealClock -> RealClock @-}
-- max :: Clock -> Clock -> Clock
-- max x y = if x < y then y else x
