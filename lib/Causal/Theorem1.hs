{-# OPTIONS_GHC "-Wno-unused-imports" #-} -- LH needs the qualified imports for SMT things
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RecordWildCards #-}
module Causal.Theorem1 where

import Language.Haskell.Liquid.ProofCombinators

import qualified Data.Assoc
import qualified Data.BinaryRelation

import qualified Redefined.Bool
import Redefined.List
import qualified Redefined.Set

import Causal.Execution.Type
import Causal.Execution.Semantics
import Causal.Execution.Reachable
import Causal.Execution.Properties


-- * Theorem 1

-- | A function which determines whether a message can be delivered.
type DeliverablePredicate p m = m -> ProcessState p m -> Bool


-- ** Causal safety property

-- | Property of a 'DeliverablePredicate' @D@ given some happens-before
-- relation @HB@, for all messages and process states meeting the
-- preconditions.
{-@
type CausallySafeProp p m HB D
    =    m1 : m
    -> { m2 : m | HB (Broadcast m1) (Broadcast m2) }
    -> { s : ProcessState p m | D m2 s }
    -> { stateDelivered s m1 }
@-}
type CausallySafeProp p m = m -> m -> ProcessState p m -> Proof


-- ** Guarded by Deliverable


-- *** Guarded by as a property

-- | Property of an 'Execution' @X@ and a 'DeliverablePredicate' @D@, for all
-- messages, processes, and process states meeting the preconditions.
{-@
type GuardedByProp p m X D
    =    m : m
    ->   p : p
    -> { s : ProcessState p m | xProcessHasStatePriorToEvent X p s (Deliver p m) }
    -> { D m s }
@-}
type GuardedByProp p m = m -> p -> ProcessState p m -> Proof


-- *** Guarded by via foldr

{-@ reflect guardedByImpl @-}
{-@ guardedByImpl :: ValidRules p m -> DeliverablePredicate p m -> Maybe (Execution p m) @-}
guardedByImpl :: (Ord p, Ord m) => [Rule p m] -> DeliverablePredicate p m -> Maybe (Execution p m)
guardedByImpl rules deliverablePredicate =
    listFoldr (guardedByImplHelper deliverablePredicate) (Just execution0) rules

{-@ reflect guardedByImplHelper @-}
guardedByImplHelper :: (Ord p, Ord m) => DeliverablePredicate p m -> Rule p m -> Maybe (Execution p m) -> Maybe (Execution p m)
guardedByImplHelper _deliverablePredicate _rule Nothing = Nothing
guardedByImplHelper _deliverablePredicate rule@BroadcastRule{} acc@Just{} = applyRulesHelper rule acc
guardedByImplHelper deliverablePredicate rule@(DeliverRule process message) acc@(Just x) =
    if deliverablePredicate message (xProcessState x process)
    then applyRulesHelper rule acc
    else Nothing

-- | Rules which produce an execution because /in addition to the premises
-- holding at each step/ a deliverable predicate @D@ holds at each step.
{-@
type RulesGuardedBy p m D =
    { rules : ValidRules p m | isJust (guardedByImpl rules D) }
@-}


-- ** Test out the props

-- | Dummy deliverable predicate used for testing the LH type aliases.
{-@ reflect exConstDP @-}
exConstDP :: DeliverablePredicate p m
exConstDP _m _s = True

{-@ exCausallySafeConst :: CausallySafeProp p m {xHappensBefore execution0} {exConstDP} @-}
exCausallySafeConst :: CausallySafeProp p m
exCausallySafeConst _m1 _m2 _s = () *** Admit

{-@ ple exRulesGuardedByConst @-}
{-@ exRulesGuardedByConst :: RulesGuardedBy p m {exConstDP} @-}
exRulesGuardedByConst :: [Rule p m]
exRulesGuardedByConst = []

{-@ exGuardedByProp :: GuardedByProp p m {execution0} {exConstDP} @-}
exGuardedByProp :: GuardedByProp p m
exGuardedByProp _m _p _s = () *** Admit


-- ** Theorem 1 proof

{-@ ple theorem1 @-}
{-@
theorem1
    ::   d : DeliverablePredicate p m
    ->  vr : ValidRules p m
    -> CausallySafeProp p m {xHappensBefore (applyValidRules vr)} {d}
    -> GuardedByProp p m {applyValidRules vr} {d}
    -> CausalDeliveryProp p m {applyValidRules vr}
@-}
theorem1
    :: (Ord p, Ord m)
    => DeliverablePredicate p m
    -> [Rule p m]
    -> CausallySafeProp p m
    -> GuardedByProp p m
    -> CausalDeliveryProp p m
theorem1 d vr csP gbP p s m1 m2
    = case statePriorTo (xProcessState x p) (Deliver p m2) of
        Nothing
            ->  xComesBefore x (Deliver p m1) (Deliver p m2) p
                -- because m2 is not delivered on p
            === True
            *** QED
        Just s'
            ->  True
            === stateDelivered s m1
            === stateDelivered s m2
                ? gbP m2 p s'
            === d m2 s'
                ? csP m1 m2 s' -- and since m1->m2
            === stateDelivered s' m1
                ? statePriorToImpliesEverInState vr p (Deliver p m2) s'
                ? stateDeliveredImpliesListElem vr p s' m1
            === listElem (Deliver p m1) s'
            === xComesBefore x (Deliver p m1) (Deliver p m2) p
            *** QED
  where
    x = applyValidRules vr
