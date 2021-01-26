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
deliveredBefore _p _a _b = False -- TODO
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

dequeueAll :: VectorClock -> DelayQueue r -> [Message r]
dequeueAll t dq =
    case dqDequeue t dq of
        Just (dq', m) -> let t' = t `vcCombine` mSent m in m : dequeueAll t' dq'
        Nothing -> []
{-@ reflect dequeueAll @-}
{-@ lazy dequeueAll @-} -- FIXME this prevents a crash

dequeueBefore :: Eq r => VectorClock -> DelayQueue r -> Message r -> Message r -> Bool
dequeueBefore t dq a b = case (listElemIndex a ms, listElemIndex b ms) of
    (Just ai, Just bi) -> ai < bi
    _ -> True -- Vacuous truth. Since it is not the case that both messages were delivered, they were (technically) delivered in the correct order.
  where
    ms = dequeueAll t dq
{-@ reflect dequeueBefore @-} -- FIXME using this instead of inline prevents a crash


-- ** Proof

-- In lieu of proving the property for the 'Process' type which requires
-- dealing with the inbox and outbox, provide a more targeted property against
-- the delay queue.
--
--      ∀ m1 m2 vt dq. loop over dq, if both m1 and m2 come out, they come out
--      in that order.

{- FIXME, this signature causes a crash:
**** LIQUID: ERROR Fixpoint.Types.dummyLoc:1:1-1:1: Error
  elaborate makeKnowledge failed on:
      (Causal.CBCAST.DelayQueue.deliverability ds_d3uS m##a2ut == Causal.CBCAST.DelayQueue.Ready) == ((if Causal.VectorClockSledge.vcLessEqual (Causal.CBCAST.Message.mSent m##a2ut) ds_d3uS then Causal.CBCAST.DelayQueue.Late else (if Causal.VectorClockSledge.vcLessEqual (Causal.CBCAST.Message.mSent m##a2ut) (Causal.VectorClockSledge.vcTick (Causal.CBCAST.Message.mSender m##a2ut) ds_d3uS) then Causal.CBCAST.DelayQueue.Ready else Causal.CBCAST.DelayQueue.Early)) == Causal.CBCAST.DelayQueue.Ready)
  with error
      Unbound symbol m##a2ut --- perhaps you meant: m##a2MT ?
-}
-- {-@
-- propDelayQueue
--     :: a:Message r
--     -> b:Message r
--     -> t:VectorClock
--     -> dq:DelayQueue r
--     -> { causallyBefore a b => dequeueBefore t dq a b }
-- @-}
propDelayQueue :: Message r -> Message r -> VectorClock -> DelayQueue r -> Proof
propDelayQueue Message{} Message{} VectorClock{} DelayQueue{}
    =   ()
    *** Admit
