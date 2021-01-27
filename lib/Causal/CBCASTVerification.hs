{-# LANGUAGE NamedFieldPuns #-}
module Causal.CBCASTVerification where

import Redefined
import Causal.CBCAST.Message
import Causal.CBCAST.Process
import Causal.CBCAST.DelayQueue
import Causal.VectorClockSledge

import Language.Haskell.Liquid.ProofCombinators (Proof, (===), (***), QED(..))


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
propProcess
    :: a:Message r
    -> b:Message r
    -> p:Process r
    -> { causallyBefore a b => deliveredBefore p a b }
@-}
propProcess :: Message r -> Message r -> Process r -> Proof
propProcess Message{} Message{} Process{}
    =   ()
    *** Admit


-- * Property for DelayQueue


-- ** Logical predicates

-- | This is the "condensed" form of CBCAST where you get rid of all the
-- process nonsense and just extract all the deliverable messages (in delivery
-- order) from the delay queue.
--
-- It's currently not 100% correct because it only does one pass.
{-@
dequeueAll :: _ -> dq:_ -> _ / [dqSize dq] @-}
dequeueAll :: VectorClock -> DelayQueue r -> [Message r]
dequeueAll t dq =
    case dqDequeue t dq of
        Just (dq', m) -> let t' = t `vcCombine` mSent m in m : dequeueAll t' dq'
        Nothing -> []
{-@ reflect dequeueAll @-}

dequeueBefore :: Eq r => VectorClock -> DelayQueue r -> Message r -> Message r -> Bool
dequeueBefore t dq a b = case (listElemIndex a ms, listElemIndex b ms) of
    (Just ai, Just bi) -> ai < bi
    _ -> True -- Vacuous truth. Since it is not the case that both messages were delivered, they were (technically) delivered in the correct order.
  where
    ms = dequeueAll t dq
{-@ inline dequeueBefore @-}


-- ** Proof

-- In lieu of proving the property for the 'Process' type which requires
-- dealing with the inbox and outbox, provide a more targeted property against
-- the delay queue.
--
--      ∀ m1 m2 vt dq. loop over dq, if both m1 and m2 come out, they come out
--      in that order.

{-@
propDelayQueue
    :: a:Message r
    -> b:Message r
    -> t:VectorClock
    -> dq:DelayQueue r
    -> { causallyBefore a b => dequeueBefore t dq a b }
@-}
propDelayQueue :: Message r -> Message r -> VectorClock -> DelayQueue r -> Proof
propDelayQueue Message{} Message{} VectorClock{} DelayQueue{}
    =   ()
    *** Admit
-- {-@ ple propDelayQueue @-}
