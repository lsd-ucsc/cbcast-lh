{-# OPTIONS_GHC "-Wno-unused-imports" #-} -- LH needs DelayQueue to be imported for specs
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RecordWildCards #-}
module Causal.CBCAST.Theorem1 where

import Language.Haskell.Liquid.ProofCombinators

import Data.Maybe (isJust, fromJust)
import Redefined
import BinaryRelation
---- import Causal.CBCAST.VectorClock
---- import Causal.CBCAST.Message
---- import qualified Causal.CBCAST.DelayQueue -- Required by LH for symbol resolution
---- import Causal.CBCAST.Process
---- import qualified Causal.CBCAST.Protocol

-- * Helper type

type Assoc k v = [(k, v)]

-- | Look for a value associated with the key.
{-@ reflect assocLookup @-}
assocLookup :: Eq k => Assoc k v -> k -> Maybe v
assocLookup assoc key = listFoldr (assocLookupHelper key) Nothing assoc
-- | Once a match is found, put it in the accumulator and then keep it there.
{-@ reflect assocLookupHelper @-}
assocLookupHelper :: Eq k => k -> (k, v) -> Maybe v -> Maybe v
assocLookupHelper key (k, v) Nothing = if key == k then Just v else Nothing
assocLookupHelper _key _item found@Just{} = found

-- | Call the function to update the value associated with the key, or insert a new one.
{-@ reflect assocUpdate @-}
assocUpdate :: Eq k => Assoc k v -> k -> (Maybe v -> v) -> Assoc k v
assocUpdate [] key f = (key, f Nothing):[]
assocUpdate ((k,v):rest) key f
    | k == key = (k,f (Just v)):rest
    | otherwise = (k,v):assocUpdate rest key f

-- | Cons one value onto the list associated with the key, or insert a singleton list.
{-@ reflect assocCons @-}
assocCons :: Eq k => Assoc k [a] -> k -> a -> Assoc k [a]
assocCons assoc key x = assocUpdate assoc key (assocConsHelper x)
-- | Cons to the list, or make a list of one.
{-@ reflect assocConsHelper @-}
assocConsHelper :: a -> Maybe [a] -> [a]
assocConsHelper x (Just xs) = x:xs
assocConsHelper x Nothing = x:[]

-- Discussion of Theorem 1 from our POPL22 submission:
--
-- Process state is defined:
--
--      "The state of a process p is the sequence of events that have occurred
--      on p. The state of p prior to a given event on p is the subsequence of
--      events on p that precede e."
--
-- Process state must facilitate answering:
--
--      * @delivered(message,state):bool@ -- Is deliver_p(m) an event in state?
--      * @deliverable(message,state):bool@ -- Can m be delivered at a process in the given state?
--      * @prior(deliver_p(m)):state@ -- Obtain state prior to delivery event.
--
-- Execution is defined:
--
--      "An execution of a distributed system consists of the set of all events
--      on all processes, together with the process order relation @->_p@ over
--      events in each process @p@ and the happens-before relation @->@ over
--      all events."
--
-- That is:
--
--      * @{Event}@ containing events all processes
--      * @Event ->_p Event@ to order events in each process
--      * @Event -> Event@ to order events by happens-before
--
-- Executions may be *guarded by* a deliverable predicate, meaning:
--
--      "We say that an execution X is guarded by a given deliverable predicate
--      if, for any message m and process p, for any deliver_p(m) event in X,
--      deliverable(m,s) holds, where s is the state of p prior to
--      deliver_p(m)."
--
-- Instead of a full execution, we will proceed with a process history, or
-- process state. Our new "guarded by" statement is:
--
--      A process history H is guarded by a given deliverable predicate if, for
--      any message m, for any deliver_p(m) in H, deliverable(m,s) holds, where
--      s is the state of p prior to deliver_p(m).

-- * Execution type

data Event p m
    = Broadcast m -- ^ broadcast(m)
    | Deliver p m -- ^ deliver_p(m)
    deriving (Eq, Ord)

type ProcessState p m = [Event p m]

data Execution p m = Execution
    { events :: Set (Event p m)
    , processes :: Assoc p (ProcessState p m)
    , happensBefore :: BinaryRelation (Event p m) (Event p m)
    }
    deriving Eq

{-@ reflect execution0 @-}
execution0 :: Execution p m
execution0 = Execution setEmpty [] setEmpty

-- * Execution semantics

data Rule p m
    = BroadcastRule p m -- A broadcast(m) event occurs on p
    | DeliverRule p m -- A deliver_p(m) event occurs

{-@ reflect ruleEvent @-}
ruleEvent :: Rule p m -> Event p m
ruleEvent (BroadcastRule p m) = Broadcast m
ruleEvent (DeliverRule p m) = Deliver p m

{-@ reflect premisesHold @-}
premisesHold :: (Eq p, Eq m) => Rule p m -> Execution p m -> Bool
premisesHold (BroadcastRule process message) Execution{..}
    = let event = ruleEvent (BroadcastRule process message)
    in not (event `setMember` events) -- The event is not already part of the execution
premisesHold (DeliverRule process message) Execution{..}
    = let event = ruleEvent (DeliverRule process message)
    in not (event `setMember` events) -- The event is not already part of the execution
    && Broadcast message `setMember` events -- There is broadcast event which corresponds to this deliver event

{-@ reflect semantics @-}
{-@ semantics :: r:Rule p m -> {s:Execution p m | premisesHold r s} -> Execution p m @-}
semantics :: (Ord p, Ord m) => Rule p m -> Execution p m -> Execution p m
semantics (BroadcastRule process message) Execution{..}
    = let event = ruleEvent (BroadcastRule process message)
    in Execution
        { events = setSingleton event `setUnion` events
        , processes = assocCons processes process event
        , happensBefore = happensBefore ---  TODO
        }
semantics (DeliverRule process message) Execution{..}
    = let event = ruleEvent (DeliverRule process message)
    in Execution
        { events = setSingleton event `setUnion` events
        , processes = assocCons processes process event
        , happensBefore = happensBefore ---  TODO
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
-- | Apply the rule via the semantics to the execution unless the premises do not hold.
{-@ reflect applyRulesHelper @-}
applyRulesHelper :: (Ord p, Ord m) => Rule p m -> Maybe (Execution p m) -> Maybe (Execution p m)
applyRulesHelper rule (Just execution) = if premisesHold rule execution then Just (semantics rule execution) else Nothing
applyRulesHelper _rule Nothing = Nothing

-- | An execution obtained by applying some rules to the initial execution.
{-@ type ReachableExecution p m = ([Rule p m], Execution p m)<{
        \rules x -> applyRules rules == Just x }> @-}
type RulesAndExecution p m = ([Rule p m], Execution p m)
{-@ type ReachableExecutionBroken p m = ([Rule p m], Execution p m)<{
        \rules x -> listFoldr semantics execution0 rules == x }> @-}

-- | Do the premises of the rule hold for each successive application of the semantics to the execution?
--
-- This more or less does the same thing as 
--
{-@ reflect premisesAlwaysHold @-}
premisesAlwaysHold :: (Ord p, Ord m) => [Rule p m] -> Bool
premisesAlwaysHold rules = tupleFirst (listFoldr premisesAlwaysHoldHelper (True, execution0) rules)
-- | If there's been no failure, show that the premises hold and apply the rule to get the next execution.
{-@ reflect premisesAlwaysHoldHelper @-}
premisesAlwaysHoldHelper :: (Ord p, Ord m) => Rule p m -> (Bool, Execution p m) -> (Bool, Execution p m)
premisesAlwaysHoldHelper rule (ok, execution)
    | ok && premisesHold rule execution = (True, semantics rule execution)
    | otherwise = (False, execution)

-- TODO: shorten this with PLE (it'll be faster to check)
{-@ reachableExecutionTailIsJust :: {re:ReachableExecution p m | fst re /= []} -> { isJust (applyRules (tail (fst re))) } @-}
reachableExecutionTailIsJust :: (Ord p, Ord m) => RulesAndExecution p m -> Proof
reachableExecutionTailIsJust (r:rs, execution) =
    case applyRules rs of
        Just _execution
            ->  ()
            *** QED
        Nothing
            ->  Just execution
            === applyRules (r:rs)
            === listFoldr applyRulesHelper (Just execution0) (r:rs)
            === applyRulesHelper r (applyRules rs)
            === applyRulesHelper r Nothing
            === Nothing
            *** QED -- contradiction

-- | Obtain the previous step in producing a reachable execution.
{-@ reachableExecutionTail :: {re:ReachableExecution p m | fst re /= []} -> ReachableExecution p m @-}
reachableExecutionTail :: (Ord p, Ord m) => RulesAndExecution p m -> RulesAndExecution p m
reachableExecutionTail (r:rs, execution') = (rs, execution)
  where
    Just execution = applyRules rs
        `proofConst` reachableExecutionTailIsJust (r:rs, execution')

{-@ ple reachableExecutionPremisesAlwaysHold @-}
{-@ reachableExecutionPremisesAlwaysHold :: re:ReachableExecution p m -> { premisesAlwaysHold (fst re) } @-}
reachableExecutionPremisesAlwaysHold :: (Ord p, Ord m) => RulesAndExecution p m -> Proof
reachableExecutionPremisesAlwaysHold (rs@[], _execution) = ()
reachableExecutionPremisesAlwaysHold (r:rs, execution)
    =   premisesAlwaysHold (r:rs)
    === tupleFirst (listFoldr premisesAlwaysHoldHelper (True, execution0) (r:rs))
    === tupleFirst (premisesAlwaysHoldHelper r (listFoldr premisesAlwaysHoldHelper (True, execution0) rs))
--      ? reachableExecutionPremisesAlwaysHold (reachableExecutionTail (r:rs, execution))
--      "no decreasing parameter"
    *** Admit


---- -- | Sequence of events on a process in reverse process-order. The head is the
---- -- most recent event. The tail is the prior process state.
---- type ProcessState r = [Event r]
---- 
---- -- | The process-order relation is expressed by the sort order in each process
---- -- state. The happens before relation is expressed by the VCs on each message
---- -- in each event.
---- type Execution r = [ProcessState r]
---- 
---- {-@ reflect isDeliver @-}
---- isDeliver :: Event r -> Bool
---- isDeliver Deliver{} = True
---- isDeliver Broadcast{} = False
---- 
---- {-@ ple priorState @-} -- One case is necessary after expanding listElem.
---- {-@ reflect priorState @-}
---- {-@ priorState :: s:ProcessState r -> {e:Event r | listElem e s} -> ProcessState r @-}
---- priorState :: Eq r => ProcessState r -> Event r -> ProcessState r
---- priorState (e:es) e'
----     | e == e' = es
----     | otherwise = priorState es e'
---- 
---- {-@
---- type GuardedByProp r X D
----     =  { e : Event r | isDeliver e }
----     -> { s : ProcessState r | listElem e s && listElem s X }
----     -> { D (eventDeliverMessage e) (priorState s e) }
---- @-}
---- type GuardedByProp r = Event r -> ProcessState r -> Proof
---- 
---- -- | Has the message been delivered? (Is the message contained in a delivery
---- -- event in the process state?)
---- {-@ reflect delivered @-}
---- delivered :: Eq r => Message r -> ProcessState r -> Bool
---- delivered eventDeliverMessage s = listElem Deliver{eventDeliverMessage} s
---- ---- | Has the message been delivered? (Is the message contained in a delivery
---- ---- event in the process state?)
---- --{-@ reflect delivered @-}
---- --delivered :: Eq r => Message r -> ProcessState r -> Bool
---- --delivered m s = listOrMap (messageMatchesEvent m) s
---- --
---- --{-@ reflect messageMatchesEvent @-}
---- --messageMatchesEvent :: Eq r => Message r -> Event r -> Bool
---- --messageMatchesEvent m Deliver{eventDeliverMessage} = m == eventDeliverMessage
---- --messageMatchesEvent m Broadcast{eventBroadcastMessage} = m == eventBroadcastMessage
---- 
---- type DeliverablePredicate r = Message r -> ProcessState r -> Bool
---- 
---- -- | Property of a 'DeliverablePredicate'.
---- {-@
---- type CausallySafeProp r D
----     =    m1 : Message r
----     -> { m2 : Message r | causallyBefore m1 m2 }
----     -> { s : ProcessState r | D m2 s }
----     -> { delivered m1 s }
---- @-}
---- type CausallySafeProp r = Message r -> Message r -> ProcessState r -> Proof
---- 
---- -- | Are all m1 before m2 delivered in that order?
---- {-@ reflect observesCausalDelivery @-}
---- observesCausalDelivery :: Execution r -> Bool
---- observesCausalDelivery _ = True -- TODO
---- 
---- -- TODO: express, somewhere, the relationship between the order of events in
---- -- process state and their "priorness"
---- --
---- -- TODO: implement observes causal delivery
---- -- 
---- -- ADD FORALL m1 m2 and p (s?) to theorem1 ???
---- --
---- -- do we need a lemma which takes m1 m2 and process state, and relates them
---- -- as in theorem1 below?
---- 
---- {-@
---- theorem1'
----     ::   d : DeliverablePredicate r
----     ->   x : Execution r
----     ->   CausallySafeProp r {d}
----     ->   GuardedByProp r {x} {d}
----     -> { s : ProcessState r | listElem s x }
----     -> {m1 : Message r | delivered m1 s }
----     -> {m2 : Message r | delivered m2 s && causallyBefore m1 m2 }
----     -> { observesCausalDelivery x }
---- @-}
---- theorem1'
----     :: DeliverablePredicate r -> Execution r -> CausallySafeProp r -> GuardedByProp r
----     -> ProcessState r -> Message r -> Message r -> Proof
---- theorem1' d execution causallySafeProp guardedByProp s m1 m2
----     = undefined
---- 
---- {-@
---- theorem1
----     ::   d : DeliverablePredicate r
----     ->   x : Execution r
----     ->   CausallySafeProp r {d}
----     ->   GuardedByProp r {x} {d}
----     -> { observesCausalDelivery x }
---- @-}
---- theorem1 :: DeliverablePredicate r -> Execution r -> CausallySafeProp r -> GuardedByProp r -> Proof
---- theorem1 = undefined
---- 
---- --{-@ processVC :: ProcCount -> ProcessState r -> VC @-}
---- --processVC :: Int -> ProcessState r -> VC
---- --processVC n [] = vcNew n
---- --processVC _ ((vc, _message):_rest) = vc
