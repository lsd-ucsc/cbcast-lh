{-# LANGUAGE NamedFieldPuns #-}
module Causal.CBCAST.Theorem1 where

import Language.Haskell.Liquid.ProofCombinators

import Redefined
import Causal.CBCAST.VectorClock
import Causal.CBCAST.Message
import qualified Causal.CBCAST.DelayQueue -- Required by LH for symbol resolution
import Causal.CBCAST.Process
import qualified Causal.CBCAST.Protocol

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

-- | Are the broadcast events of the messages ordered under happens before?
{-@ reflect causallyBefore @-}
causallyBefore :: Message r -> Message r -> Bool
causallyBefore m1 m2 = mSent m1 `vcLess` mSent m2

data Event r
    = Broadcast -- ^ Not used in proof
        { eventBroadcastMessage :: Message r -- ^ Message which was broadcast
        }
    | Deliver -- ^ A `deliver_p(m)` event
        { eventDeliverMessage :: Message r -- ^ Message which was delivered
        }
    deriving Eq
{-@ measure eventBroadcastMessage :: Event r -> Message r @-}
{-@ measure eventDeliverMessage :: Event r -> Message r @-}

-- | Sequence of events on a process in reverse process-order. The head is the
-- most recent event. The tail is the prior process state.
type ProcessState r = [Event r]

-- | The process-order relation is expressed by the sort order in each process
-- state. The happens before relation is expressed by the VCs on each message
-- in each event.
type Execution r = [ProcessState r]

{-@ reflect isDeliver @-}
isDeliver :: Event r -> Bool
isDeliver Deliver{} = True
isDeliver Broadcast{} = False

{-@ ple priorState @-} -- One case is necessary after expanding listElem.
{-@ reflect priorState @-}
{-@ priorState :: s:ProcessState r -> {e:Event r | listElem e s} -> ProcessState r @-}
priorState :: Eq r => ProcessState r -> Event r -> ProcessState r
priorState (e:es) e'
    | e == e' = es
    | otherwise = priorState es e'

{-@
type GuardedByProp r X D
    =  { e : Event r | isDeliver e }
    -> { s : ProcessState r | listElem e s && listElem s X }
    -> { D (eventDeliverMessage e) (priorState s e) }
@-}
type GuardedByProp r = Event r -> ProcessState r -> Proof

-- | Has the message been delivered? (Is the message contained in a delivery
-- event in the process state?)
{-@ reflect delivered @-}
delivered :: Eq r => Message r -> ProcessState r -> Bool
delivered m s = listOrMap (messageMatchesEvent m) s

{-@ reflect messageMatchesEvent @-}
messageMatchesEvent :: Eq r => Message r -> Event r -> Bool
messageMatchesEvent m Deliver{eventDeliverMessage} = m == eventDeliverMessage
messageMatchesEvent m Broadcast{eventBroadcastMessage} = m == eventBroadcastMessage

type DeliverablePredicate r = Message r -> ProcessState r -> Bool

-- | Property of a 'DeliverablePredicate'.
{-@
type CausallySafeProp r D
    =    m1 : Message r
    -> { m2 : Message r | causallyBefore m1 m2 }
    -> { s : ProcessState r | D m2 s }
    -> { delivered m1 s }
@-}
type CausallySafeProp r = Message r -> Message r -> ProcessState r -> Proof

-- | Are all m1 before m2 delivered in that order?
{-@ reflect observesCausalDelivery @-}
observesCausalDelivery :: Execution r -> Bool
observesCausalDelivery _ = True -- TODO

{-@
theorem1
    ::   d : DeliverablePredicate r
    ->   x : Execution r
    ->   CausallySafeProp r {d}
    ->   GuardedByProp r {x} {d}
    -> { observesCausalDelivery x }
@-}
theorem1 :: DeliverablePredicate r -> Execution r -> CausallySafeProp r -> GuardedByProp r -> Proof
theorem1 = undefined

--{-@ processVC :: ProcCount -> ProcessState r -> VC @-}
--processVC :: Int -> ProcessState r -> VC
--processVC n [] = vcNew n
--processVC _ ((vc, _message):_rest) = vc
