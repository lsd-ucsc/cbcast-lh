module Causal.Execution.Semantics where
-- Semantics to construct a well-formed execution.

import Redefined.Set

import Data.Assoc
import Data.BinaryRelation

import Causal.Execution.Type

data Rule p m
    = BroadcastRule p m -- A broadcast(m) event occurs on p
    | DeliverRule p m -- A deliver_p(m) event occurs

-- | Convert a rule in the semantics to a corresponding event in an execution.
-- This is necessary because both rules require a process, but not both events.
{-@ reflect ruleEvent @-}
ruleEvent :: Rule p m -> Event p m
ruleEvent (BroadcastRule _p m) = Broadcast m
ruleEvent (DeliverRule p m) = Deliver p m

{-@ reflect premisesHold @-}
premisesHold :: (Ord p, Ord m) => Rule p m -> Execution p m -> Bool
premisesHold rule@(BroadcastRule _process _message) x =
    let event = ruleEvent rule
    in not (event `setMember` xEvents x) -- The event is not already part of the execution
premisesHold rule@(DeliverRule _process message) x =
    let event = ruleEvent rule
    in not (event `setMember` xEvents x) -- The event is not already part of the execution
    && Broadcast message `setMember` xEvents x-- There is already a broadcast event for this message

{-@ reflect semantics @-}
{-@ semantics :: r:Rule p m -> {s:Execution p m | premisesHold r s} -> Execution p m @-}
semantics :: (Ord p, Ord m) => Rule p m -> Execution p m -> Execution p m
semantics rule@(BroadcastRule process _message) x =
    let event = ruleEvent rule
    in Execution
        { xProcesses = assocCons (xProcesses x) process event
        , xEventOrder = xEventOrder x -- Existing pairs
            `setUnion` (setFromList (xProcessState x process) `brWithDomain` event) -- process history is before new event
        }
semantics rule@(DeliverRule process message) x =
    let event = ruleEvent rule
    in Execution
        { xProcesses = assocCons (xProcesses x) process event
        , xEventOrder = xEventOrder x
            `setUnion` setSingleton (Broadcast message, event) -- message broadcast is before new event
            `setUnion` (setFromList (xProcessState x process) `brWithDomain` event) -- process history is before new event
        }
