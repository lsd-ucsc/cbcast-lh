{-# LANGUAGE NamedFieldPuns #-}
module Causal.Isomorphism where

import Language.Haskell.Liquid.ProofCombinators

import Redefined.Proof
import Redefined.Function
import Redefined.Bool
import Redefined.Tuple
import Redefined.List
import qualified Redefined.Set

import qualified Data.Assoc
import qualified Data.BinaryRelation

import Causal.Execution.Type
import Causal.Execution.Semantics
import Causal.Execution.Reachable

import Causal.CBCAST.VectorClock

{-@
isomorphism
    ::   vr : ValidRules p m

    ->   p1 : p
    ->   e1 : Event p m
    -> { s1 : ProcessState p m | Just s1 == xStateAtEvent (applyValidRules vr) p1 e1 }

    ->   p2 : p
    ->   e2 : Event p m
    -> { s2 : ProcessState p m | Just s2 == xStateAtEvent (applyValidRules vr) p2 e2 }

    -> { xHappensBefore (applyValidRules vr) e1 e2
     <=> vcLess (shim procCount s1) (shim procCount s2)
       }
@-}
isomorphism
    :: [Rule p m]
    -> p -> Event p m -> ProcessState p m
    -> p -> Event p m -> ProcessState p m
    -> Proof
isomorphism vr p1 e1 s1 p2 e2 s2 = () *** Admit

{-@ reflect shim @-}
shim :: Int -> ProcessState p m -> VC
shim size _s = vcNew size -- FIXME
