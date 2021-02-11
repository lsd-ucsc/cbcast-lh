{-# LANGUAGE NamedFieldPuns #-}
module Causal.CBCAST.Verification where

import Causal.VectorClock
import Causal.CBCAST.Message

import Language.Haskell.Liquid.ProofCombinators
    (Proof, QED(..), (***))

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

causallyBefore :: Message r -> Message r -> Bool
causallyBefore a b = mSent a `vcLess` mSent b
{-@ inline causallyBefore @-}

-- page 11/282:
--
--      "Observe first that m_1 -> m_2, hence VT(m_1) < VT(m_2) (basic property
--      of vector times)."

{-@ basicPropertyOfVectorClocks :: m1:Message r -> {m2:Message r | causallyBefore m1 m2} -> { vcLess (mSent m1) (mSent m2) } @-}
basicPropertyOfVectorClocks :: Message r -> Message r -> Proof
basicPropertyOfVectorClocks Message{} Message{} = () *** QED

-- page 8/279:
--
--      "Two types of delivery ordering will be of interest here. We define the
--      causal delivery ordering for multicast messages m and m' as follows:
--
--          m -> m' => for-all p element-of dests(m) intersect dests(m'):
--                      deliver(m) ->^p deliver(m')
--
--      CBCAST provides only the causal delivery ordering."

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

{-@ ignore proofSafety @-} -- TODO this takes forever
{-@ ple proofSafety @-}
{-@
proofSafety
    :: t:VC
    -> {m1:Message r | deliverable m1 t}
    -> {m2:Message r | causallyBefore m1 m2}
    -> {not (deliverable m2 t)}
@-}
proofSafety :: VC -> Message r -> Message r -> Proof
proofSafety _ _ _ = () *** QED
