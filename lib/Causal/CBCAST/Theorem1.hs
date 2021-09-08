{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RecordWildCards #-}
module Causal.CBCAST.Theorem1 where

import Language.Haskell.Liquid.ProofCombinators

import Data.Maybe (isJust, fromJust)
import Redefined
import BinaryRelation


-- * Execution type

data Event p m
    = Broadcast {broadcastMessage::m} -- ^ broadcast(m)
    | Deliver {deliverProcess::p, deliverMessage::m} -- ^ deliver_p(m)
    deriving (Eq, Ord)
{-@
data Event p m
    = Broadcast {broadcastMessage::m}
    | Deliver {deliverProcess::p, deliverMessage::m}
@-} -- To create measures for each field.

-- | Events in reverse order of their taking place on the process. New events
-- are cons'd to the left. The tail is prior process state.
type ProcessState p m = [Event p m]

data Execution p m = Execution
    { events :: Set (Event p m)
    , processes :: Assoc p (ProcessState p m)
    , happensBeforeRelation :: BinaryRelation (Event p m) (Event p m)
    }
{-@
data Execution p m = Execution
    { events :: Set (Event p m)
    , processes :: Assoc p (ProcessState p m)
    , happensBeforeRelation :: BinaryRelation (Event p m) (Event p m)
    }
@-} -- To create measures for each field.

{-@ reflect execution0 @-}
execution0 :: Execution p m
execution0 = Execution setEmpty [] setEmpty


-- * Execution semantics

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
premisesHold :: (Eq p, Eq m) => Rule p m -> Execution p m -> Bool
premisesHold rule@(BroadcastRule process message) Execution{..}
    = let event = ruleEvent rule
    in not (event `setMember` events) -- The event is not already part of the execution
    -- TODO
premisesHold rule@(DeliverRule process message) Execution{..}
    = let event = ruleEvent rule
    in not (event `setMember` events) -- The event is not already part of the execution
    && Broadcast message `setMember` events -- There is broadcast event which corresponds to this deliver event
    -- TODO

{-@ reflect semantics @-}
{-@ semantics :: r:Rule p m -> {s:Execution p m | premisesHold r s} -> Execution p m @-}
semantics :: (Ord p, Ord m) => Rule p m -> Execution p m -> Execution p m
semantics rule@(BroadcastRule process message) Execution{..}
    = let event = ruleEvent rule
    in Execution
        { events = setSingleton event `setUnion` events
        , processes = assocCons processes process event
        , happensBeforeRelation = happensBeforeRelation ---  TODO
        }
semantics rule@(DeliverRule process message) Execution{..}
    = let event = ruleEvent rule
    in Execution
        { events = setSingleton event `setUnion` events
        , processes = assocCons processes process event
        , happensBeforeRelation = happensBeforeRelation ---  TODO
        }


-- * Reachable execution

-- | Apply the rules via the semantics in foldr/cons-order to obtain a final
-- execution, unless the premises of some rule for some intermediate execution
-- do not hold.
--
-- (foldr f x [a,b,c]) is like (f a (f b (f c x)))
--
{-@ reflect applyRules @-}
applyRules :: (Ord p, Ord m) => [Rule p m] -> Maybe (Execution p m)
applyRules rules = listFoldr applyRulesHelper (Just execution0) rules
-- | Apply the rule via the semantics to the execution, unless the premises do
-- not hold or there's already no execution.
{-@ reflect applyRulesHelper @-}
applyRulesHelper :: (Ord p, Ord m) => Rule p m -> Maybe (Execution p m) -> Maybe (Execution p m)
applyRulesHelper rule (Just execution) = if premisesHold rule execution then Just (semantics rule execution) else Nothing
applyRulesHelper _rule Nothing = Nothing

-- | Rules in reverse order of their application to an execution. Rules applied
-- later are cons'd to the left.
{-@
type ValidRules p m =
    { rules : [Rule p m] |
        isJust (applyRules rules)
    }
@-}

{-@ reflect applyValidRules @-}
{-@ applyValidRules :: (Ord p, Ord m) => ValidRules p m -> Execution p m @-}
applyValidRules :: (Ord p, Ord m) => [Rule p m] -> Execution p m
applyValidRules rules = case applyRules rules of
    Just execution -> execution

{-@ ple validRulesAreDeep @-}
{-@ validRulesAreDeep
        :: { rules : ValidRules p m | rules /= [] }
        -> { isJust (applyRules (tail rules)) } @-}
validRulesAreDeep :: (Ord p, Ord m) => [Rule p m] -> Proof
validRulesAreDeep (r:rs) = case applyRules rs of
    Just _execution -> () *** QED
    Nothing
        ->  isJust (applyRules (r:rs)) -- premise
        === isJust (applyRulesHelper r (applyRules rs))
        === isJust (applyRulesHelper r Nothing) -- by the case split
        === isJust Nothing
        *** QED

---- -- Causes LH crash
---- {-@
---- using [Rule p m] as
----     { rules : [Rule p m] |
----         isJust (applyRules rules) && rules /= []
----             => isJust (applyRules (tail rules))
----     }
---- @-}

{-@ reflect validRulesTail @-}
{-@ validRulesTail :: {rules:ValidRules p m | rules /= []} -> ValidRules p m @-}
validRulesTail :: (Ord p, Ord m) => [Rule p m] -> [Rule p m]
validRulesTail (r:rs) = rs `proofConst` validRulesAreDeep (r:rs)

{-@ ple rulesEx0 @-}
{-@ rulesEx0 :: ValidRules p m @-}
rulesEx0 :: [Rule p m]
rulesEx0 = []

{-@ ple rulesEx1 @-}
{-@ rulesEx1 :: ValidRules Int String @-}
rulesEx1 :: [Rule Int String]
rulesEx1 = [BroadcastRule 1 "hello world"]

{-@ ple rulesEx2 @-}
{-@ rulesEx2 :: ValidRules Int String @-}
rulesEx2 :: [Rule Int String]
rulesEx2 = tail [BroadcastRule 1 "hello world"]

---- -- LH doesn't know that rulesEx1 /= [] ??
---- {-@ ple rulesEx3 @-}
---- {-@ rulesEx3 :: ValidRules Int String @-}
---- rulesEx3 :: [Rule Int String]
---- rulesEx3 = validRulesTail rulesEx1


-- * Theorem 1

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
eventDeliversMessage message (Broadcast _m) = False

-- | Property of a 'DeliverablePredicate' @D@ given some happens-before
-- relation @HB@.
{-@
type CausallySafeProp p m HB D
    =    m1 : m
    -> { m2 : m | HB m1 m2 }
    -> { s : ProcessState p m | D m2 s }
    -> { delivered m1 s }
@-}
type CausallySafeProp p m = m -> m -> ProcessState p m -> Proof


-- ** Guarded by Deliverable

{-@ reflect isDeliver @-}
isDeliver :: Event p m -> Bool
isDeliver Deliver{} = True
isDeliver Broadcast{} = False
{-@
type GuardedByProp p m X D
    =  { e : Event p m | isDeliver e && assocKey (processes X) (deliverProcess e) }
    -> { s : ProcessState p m | listElem e s && s == assocKeyLookup (processes X) (deliverProcess e) }
    -> { D (deliverMessage e) (tailAfter e s) }
@-}
type GuardedByProp p m = Event p m -> ProcessState p m -> Proof


-- ** Test out the props

-- | Dummy deliverable predicate used for testing the LH type aliases.
{-@ reflect exConstHB @-}
exConstHB :: m -> m -> Bool
exConstHB _m1 _m2 = True

-- | Dummy deliverable predicate used for testing the LH type aliases.
{-@ reflect exConstDP @-}
exConstDP :: DeliverablePredicate p m
exConstDP _m _s = True

{-@ exCausallySafeConst :: CausallySafeProp p m {exConstHB} {exConstDP} @-}
exCausallySafeConst :: CausallySafeProp p m
exCausallySafeConst _m1 _m2 _s = () *** Admit

{-@ exExecution0GuardedByConst :: GuardedByProp p m {execution0} {exConstDP} @-}
exExecution0GuardedByConst :: GuardedByProp p m
exExecution0GuardedByConst e s = () *** Admit


-- ** Theorem1Prop

{-@ reflect happensBefore @-}
happensBefore :: (Eq m, Eq p) => Execution p m -> m -> m -> Bool
happensBefore Execution{happensBeforeRelation} m1 m2
    = setMember (Broadcast m1, Broadcast m2) happensBeforeRelation

-- | Are all m1 before m2 delivered in that order?
{-@ reflect observesCausalDelivery @-}
observesCausalDelivery :: Execution p m -> Bool
observesCausalDelivery _ = True -- TODO

{-@
theorem1One
    ::   d : DeliverablePredicate p m
    ->  vr : ValidRules p m
    -> { x : Execution p m | x == applyValidRules vr }
    ->   CausallySafeProp p m {happensBefore x} {d}
    ->   GuardedByProp p m {x} {d}
    -> { p : p | assocKey (processes x) p }
    -> { s : ProcessState p m | s == assocKeyLookup (processes x) p }
    -> {m1 : m | delivered m1 s }
    -> {m2 : m | delivered m2 s && happensBefore x m1 m2 }
    -> { observesCausalDelivery x }
@-}
theorem1One
    :: DeliverablePredicate p m -> [Rule p m] -> Execution p m -> CausallySafeProp p m -> GuardedByProp p m
    -> p -> ProcessState p m -> m -> m -> Proof
theorem1One _d _vr _x _csP _gbP _p _s _m1 _m2 = () *** Admit -- TODO

{-@
theorem1
    ::   d : DeliverablePredicate p m
    ->  vr : ValidRules p m
    ->   CausallySafeProp p m {happensBefore (applyValidRules vr)} {d}
    ->   GuardedByProp p m {(applyValidRules vr)} {d}
    -> { observesCausalDelivery (applyValidRules vr) }
@-}
theorem1
    :: DeliverablePredicate p m -> [Rule p m] -> CausallySafeProp p m -> GuardedByProp p m
    -> Proof
theorem1 _d _vr _csP _gbP = () *** Admit -- TODO: iterate over all processes, states, and pairs of messages calling theorem1One


-- * Helper functions

{-@ reflect tailAfter @-}
{-@ ple tailAfter @-} -- To show `listElem t (x:xs) && t /= x => listElem t xs`
{-@ tailAfter :: t:a -> {xs:[a] | listElem t xs} -> [a] @-}
tailAfter :: Eq a => a -> [a] -> [a]
tailAfter _target [] = []
tailAfter target (x:xs) = if target == x then xs else tailAfter target xs


-- * Helper Assoc list type
