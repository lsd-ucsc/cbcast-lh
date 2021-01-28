{-# LANGUAGE NamedFieldPuns #-}
module Causal.CBCASTVerification where

import Redefined
import Causal.CBCAST.Message
import Causal.CBCAST.Process
import Causal.CBCAST.DelayQueue
import Causal.VectorClockSledge

import Language.Haskell.Liquid.ProofCombinators (Proof, (===), (***))
import qualified Language.Haskell.Liquid.ProofCombinators as Proof


-- * Property for Process


-- ** Logical predicates

-- page 7/278:
--
--      "The execution of a process is a partial ordered sequence of _events_,
--      each corresponding to the execution of an indivisible action. An
--      acyclic event order, denoted ->^p, reflects the dependence of events
--      occuring at process p upon one another."
--
--      "As Lamport [17], we define the potential causality relation for the
--      system, ->, as the transitive closure of the relation defined as
--      follows:
--
--      (1) if there-exists p: e ->^p e' then e -> e'
--      (2) for-all m: send(m) -> rcv(m)"
--
--      "For messages m and m', the notation m -> m' will be used as a
--      shorthand for send(m) -> send(m')."

-- page 11/282:
--
--      "Observe first that m_1 -> m_2, hence VT(m_1) < VT(m_2) (basic property
--      of vector times)."

causallyBefore :: Message r -> Message r -> Bool
causallyBefore a b = mSent a `vcLess` mSent b
{-@ inline causallyBefore @-}

-- page 8/279:
--
--      "Two types of delivery ordering will be of interest here. We define the
--      causal delivery ordering for multicast messages m and m' as follows:
--
--          m -> m' => for-all p element-of dests(m) intersect dests(m'):
--                      deliver(m) ->^p deliver(m')
--
--      CBCAST provides only the causal delivery ordering."

deliveredBefore :: Process r -> Message r -> Message r -> Bool
deliveredBefore _p _a _b = False -- TODO: not implemented because we're focusing on the dq proof first
{-@ inline deliveredBefore @-}


-- ** Proof

-- page 10/281:
--
--      "Suppose that a set of processes P communicate using only broadcasts to
--      the full set of processes in the system; that is,
--      for-all m: dests(m) = P."
--
--      "We now develop a _delivery protocol_ by which each process p receives
--      messages sent to it, delays them if necessary, and then delivers them
--      in an order consistent with causality:
--
--          m -> m' => for-all p: deliver_p(m) ->^p deliver_p(m')"

{-@
prop1
    ::   a:Message r
    -> { b:Message r | causallyBefore a b }
    ->   p:Process r
    -> { _:Proof | deliveredBefore p a b }
@-}
prop1 :: Message r -> Message r -> Process r -> Proof
prop1 Message{} Message{} Process{}
    =   ()
    *** Proof.Admit


-- * Property for DelayQueue


-- ** Logical predicates

-- | Return the list of all deliverable messages (in delivery order) for a
-- process represented by the vector-time and delay-queue.
--
-- This is like "CBCAST lite" because no sending or receiving occurs, and so we
-- can regard the list of all deliverable messages as a constant property of
-- the process represented by the vector-time and delay-queue.
{-@
allDeliverableMessages :: _ -> dq:_ -> _ / [dqSize dq] @-}
allDeliverableMessages :: VectorClock -> DelayQueue r -> [Message r]
allDeliverableMessages t dq =
    case dqDequeue t dq of
        Just (dq', m) -> let t' = t `vcCombine` mSent m in m : allDeliverableMessages t' dq'
        Nothing -> []
{-@ reflect allDeliverableMessages @-}

-- | Has the message been received at a process represented by the delay-queue?
messageIsReceived :: Eq r => DelayQueue r -> Message r -> Bool
messageIsReceived (DelayQueue xs) m = listElem m xs
{-@ inline messageIsReceived @-}

-- | Is the message deliverable at a process represented by the vector-time and
-- delay-queue?
messageIsDeliverable :: Eq r => VectorClock -> DelayQueue r -> Message r -> Bool
messageIsDeliverable t dq m = listElem m (allDeliverableMessages t dq)
{-@ inline messageIsDeliverable @-}

{-@
deliverableBefore
    ::   t:_
    ->   dq:_
    -> { a:_ | messageIsDeliverable t dq a }
    -> { b:_ | messageIsDeliverable t dq b }
    -> _
@-}
deliverableBefore :: Eq r => VectorClock -> DelayQueue r -> Message r -> Message r -> Bool
deliverableBefore t dq a b = aMessageIndex < bMessageIndex
  where
    deliverableMessages = allDeliverableMessages t dq
    Just aMessageIndex = listElemIndex a deliverableMessages
    Just bMessageIndex = listElemIndex b deliverableMessages
---- {-@ inline deliverableBefore @-}


-- ** Proof

-- | A warmup proof that a deliverable message is received.
{-@
prop_DeliverableImpliesReceived
    ::   t:VectorClock
    ->   dq:DelayQueue r
    -> { m:Message r | messageIsDeliverable t dq m }
    -> { _:Proof | messageIsReceived dq m }
@-}
{-@ ple prop_DeliverableImpliesReceived @-}
prop_DeliverableImpliesReceived :: Eq r => VectorClock -> DelayQueue r -> Message r -> Proof
prop_DeliverableImpliesReceived _ (DelayQueue xs) m
    =   listElem m xs
    *** Proof.Admit

---- -- | Instead of proving the property for the 'Process' type which requires
---- -- dealing with the inbox and outbox, provide a more targeted property against
---- -- a process represented by a vector-time and delay-queue.
---- --
---- --      ∀ m1 m2 vt dq. loop over dq, if both m1 and m2 come out, they come out
---- --      in that order.
---- {-@
---- prop2
----     ::   a:Message r
----     -> { b:Message r | causallyBefore a b }
----     ->   t:VectorClock
----     -> { dq:DelayQueue r | messageIsDeliverable t dq a && messageIsDeliverable t dq b }
----     -> { _:Proof | deliverableBefore t dq a b }
---- @-}
---- prop2 :: Message r -> Message r -> VectorClock -> DelayQueue r -> Proof
---- prop2 Message{} Message{} VectorClock{} DelayQueue{}
----     -- niki: if PLE doesn't work, follow the strucure of the postcondition..
----     -- niki: start with the case and proof
----     -- niki: for recursive functions, you'll need to call their proofs recursively
----     --
----     -- lindsey: (??) add to precondition that the messages are delivered
----     =   ()
----     *** Proof.Admit
---- {-@ ple prop2 @-}
