{-# OPTIONS_GHC "-Wno-unused-imports" #-} -- LH needs Redefined to be imported for specs
-- | Implementation of vector clocks and safety proof for deliverability
-- predicate. Safety proof uses implementation components as part of the spec.
module Causal.CBCAST.Verification where

import Language.Haskell.Liquid.ProofCombinators

import Redefined
import Causal.CBCAST.VectorClock
import Causal.CBCAST.Message

-- | page 7/278:
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
--
-- Therefore 'causallyBeforeK' is an alias for 'vcLessK' with respect to
-- message sent times.
--
{-@ reflect causallyBeforeK @-}
{-@
causallyBeforeK :: Message r -> Message r -> PID -> Bool @-}
causallyBeforeK :: Message r -> Message r -> PID -> Bool
causallyBeforeK m1 m2 k = vcLessK (mSent m1) (mSent m2) k

-- | Property: 'causallyBeforeK' is true at all indexes.
{-@
type CausallyBeforeProp M1 M2 = k:PID -> { _:Proof | causallyBeforeK M1 M2 k } @-}
type CausallyBeforeProp = PID -> Proof

-- | Property: 'deliverableK' is true at all indexes.
{-@
type DeliverableProp M P = k:PID -> { _:Proof | deliverableK M P k } @-}
type DeliverableProp = PID -> Proof

-- | @processOrderAxiom@ says that every message sent by a given process has a
-- unique VC value at the sender position. (This follows from the fact that
-- events on a process have a total order.) This is enough to prove safety in
-- the same-sender case, because we already know that m1 -> m2, so we know that
-- for each position i in their respective VCs, VC(m1)[i] <= VC(m2)[i]. This
-- axiom rules out the case where they're equal, so then we know that VC(m1)[i]
-- < VC(m2)[i], which is the fact that LH needs to complete the proof.
{-@
assume processOrderAxiom
    ::  m1 : Message r
    ->  m2 : Message r
    ->  { _:Proof | mSender m1 == mSender m2 }
    ->  { _:Proof | vcReadK (mSent m1) (mSender m1) != vcReadK (mSent m2) (mSender m2) }
@-}
processOrderAxiom :: Message r -> Message r -> Proof -> Proof
processOrderAxiom _m1 _m2 _proof = ()

-- | page 8/279:
--
--      "Two types of delivery ordering will be of interest here. We define the
--      causal delivery ordering for multicast messages m and m' as follows:
--
--          m -> m' => for-all p element-of dests(m) intersect dests(m'):
--                      deliver(m) ->^p deliver(m')
--
--      CBCAST provides only the causal delivery ordering."
--
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
--
{-@ ple safetyProof @-}
{-@
safetyProof
    ::  p : Proc
    ->  m1 : Message r
    ->  m2 : Message r
    ->  DeliverableProp m1 p
    ->  CausallyBeforeProp m1 m2
    ->  DeliverableProp m2 p
    ->  { _:Proof | false}
@-}
safetyProof :: Proc -> Message r -> Message r -> DeliverableProp -> CausallyBeforeProp -> DeliverableProp -> Proof
safetyProof _p m1 m2 m1_d_p m1_before_m2 m2_d_p
    | mSender m1 == mSender m2
        =   ()
            ? m1_d_p (mSender m1)
            ? m2_d_p (mSender m2)
            ? processOrderAxiom m1 m2 ()
            *** QED
    | otherwise
        =   ()
            ? m1_before_m2 (mSender m1)
            ? m1_d_p (mSender m1)
            ? m2_d_p (mSender m1)
            *** QED
