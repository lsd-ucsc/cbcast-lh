{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RecordWildCards #-}
module Causal.Theorem1 where

import Language.Haskell.Liquid.ProofCombinators

import Data.Assoc
import Data.BinaryRelation

import Redefined.Tuple
import Redefined.List
import Redefined.Set

import Causal.Execution.Type
import Causal.Execution.Semantics
import Causal.Execution.Reachable


-- * Theorem 1

-- | A function which determines whether a message can be delivered.
type DeliverablePredicate p m = m -> ProcessState p m -> Bool


-- ** Causally Safe

-- | Has the message been delivered? (Is the message contained in a delivery
-- event in the process state?)
{-@ reflect delivered @-}
delivered :: Eq m => m -> ProcessState p m -> Bool
delivered m s = listOrMap (eventDeliversMessage m) s

-- | Is the event a delivery of the message?
{-@ reflect eventDeliversMessage @-}
eventDeliversMessage :: Eq m => m -> Event p m -> Bool
eventDeliversMessage message (Deliver _p m) = message == m
eventDeliversMessage _message (Broadcast _m) = False

-- | Property of a 'DeliverablePredicate' @D@ given some happens-before
-- relation @HB@.
{-@
type CausallySafeProp p m HB D
    =    m1 : m
    -> { m2 : m | HB (Broadcast m1) (Broadcast m2) }
    -> { s : ProcessState p m | D m2 s }
    -> { delivered m1 s }
@-}
type CausallySafeProp p m = m -> m -> ProcessState p m -> Proof


-- ** Guarded by Deliverable

{-@ guardedByImpl :: ValidRules p m -> DeliverablePredicate p m -> Maybe (Execution p m) @-}
guardedByImpl :: (Ord p, Ord m) => [Rule p m] -> DeliverablePredicate p m -> Maybe (Execution p m)
guardedByImpl rules deliverablePredicate =
    listFoldr (guardedByImplHelper deliverablePredicate) (Just execution0) rules

guardedByImplHelper :: (Ord p, Ord m) => DeliverablePredicate p m -> Rule p m -> Maybe (Execution p m) -> Maybe (Execution p m)
guardedByImplHelper _deliverablePredicate _rule Nothing = Nothing
guardedByImplHelper _deliverablePredicate rule@BroadcastRule{} acc@Just{} = applyRulesHelper rule acc
guardedByImplHelper deliverablePredicate rule@(DeliverRule process message) acc@(Just x) =
    if deliverablePredicate message (xProcessState x process)
    then applyRulesHelper rule acc
    else Nothing

