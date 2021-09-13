module Causal.Execution.Semantics where

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

-- {-@ reflect premisesHold @-}
-- premisesHold :: (Eq p, Eq m) => Rule p m -> Execution p m -> Bool
-- premisesHold rule@(BroadcastRule _process _message) Execution{..}
--     = let event = ruleEvent rule
--     in not (event `setMember` events) -- The event is not already part of the execution
--     -- TODO
-- premisesHold rule@(DeliverRule _process message) Execution{..}
--     = let event = ruleEvent rule
--     in not (event `setMember` events) -- The event is not already part of the execution
--     && Broadcast message `setMember` events -- There is broadcast event which corresponds to this deliver event
--     -- TODO

