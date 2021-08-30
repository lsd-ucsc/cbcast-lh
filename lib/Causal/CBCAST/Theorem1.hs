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

data Event r
    = Broadcast -- ^ A broadcast event; Not used in the proof
    | Delivery -- ^ A delivery event
        { deliveryP :: Process r -- ^ The process just prior to delivery
        , deliveryM :: Message r -- ^ The message which is delivered
        }
    deriving Eq
{-@ measure deliveryP :: Event r -> Process r @-}
{-@ measure deliveryM :: Event r -> Message r @-}

type ProcessState r = (Process r, [Event r])

-- | Is the event a delivery event contained in the process state?
{-@ reflect delivery @-}
{-@ delivery :: Event r -> ProcessState r -> Bool @-}
delivery :: Eq r => Event r -> ProcessState r -> Bool
delivery Broadcast _ = False
delivery e@Delivery{} (_p, es) = listElem e es

-- | Has the message been delivered? (Is the message contained in a delivery
-- event in the process state?)
{-@ reflect delivered @-}
delivered :: Eq r => Message r -> ProcessState r -> Bool
delivered m (_p, es) = listOrMap (messageMatchesDelivery m) es

-- | Is the event a delivery, and does it contain the message?
{-@ reflect messageMatchesDelivery @-}
messageMatchesDelivery :: Eq r => Message r -> Event r -> Bool
messageMatchesDelivery m Broadcast = False
messageMatchesDelivery m Delivery{deliveryM} = m == deliveryM

{-@ reflect causallyBefore @-}
causallyBefore :: Message r -> Message r -> Bool
causallyBefore m1 m2 = mSent m1 `vcLess` mSent m2

{-@ reflect observesCausalDelivery @-}
observesCausalDelivery :: ProcessState r -> Bool
observesCausalDelivery _ = True

type DeliverablePredicate r = Message r -> ProcessState r -> Bool

{-@
type CausallySafeProp r D
    =    m1 : Message r
    -> { m2 : Message r | causallyBefore m1 m2 }
    -> { s : ProcessState r | D m2 s }
    -> { delivered m1 s }
@-}
type CausallySafeProp r = Message r -> Message r -> ProcessState r -> Proof

{-@
type GuardedByProp r S D
    =  { e : Event r | delivery e S }
    -> { D (deliveryM e) (deliveryP e, []) }
@-}
type GuardedByProp r = Event r -> Proof

{-@
theorem1
    ::   d : DeliverablePredicate r
    ->   s : ProcessState r
    ->   CausallySafeProp r {d}
    ->   GuardedByProp r {s} {d}
    -> { observesCausalDelivery s }
@-}
theorem1 :: DeliverablePredicate r -> ProcessState r -> CausallySafeProp r -> GuardedByProp r -> Proof
theorem1 = undefined
