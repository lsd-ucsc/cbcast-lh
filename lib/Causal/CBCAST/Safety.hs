{-# OPTIONS_GHC "-Wno-unused-imports" #-} -- LH needs Redefined to be imported for specs
-- | Implementation of vector clocks and safety proof for deliverability
-- predicate. Safety proof uses implementation components as part of the spec.
--
-- To follow the proof, start with VectorClock.hs, then Message.hs, then this
-- file.
module Causal.CBCAST.Safety where

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

{-@ reflect causallyBefore @-}
{-@
causallyBefore :: Message r -> Message r -> Bool @-}
causallyBefore :: Message r -> Message r -> Bool
causallyBefore m1 m2 = vcLess (mSent m1) (mSent m2)

-- | Property: 'causallyBeforeK' is true at all indexes.
{-@
type CausallyBeforePropK M1 M2 = k:PID -> { _:Proof | causallyBeforeK M1 M2 k } @-}
type CausallyBeforePropK = PID -> Proof

-- | Property: 'deliverableK' is true at all indexes.
{-@
type DeliverablePropK M P = k:PID -> { _:Proof | deliverableK M P k } @-}
type DeliverablePropK = PID -> Proof

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
-- The actual property we're proving, however, is the "causal safety
-- of delivery" property about our deliverable predicate.

{-@
iterImpliesForall
    :: n:Nat
    -> p:(Fin {n} -> Bool)
    -> { _:Proof | iter n p }
    -> (k:Fin {n} -> { _:Proof | p k })
@-}
iterImpliesForall :: Int -> (Fin -> Bool) -> Proof -> (Fin -> Proof)
iterImpliesForall n p satisfied k = () *** Admit

{-@
d_implies_dk
    ::  procVc: VC
    ->  m : Message r
    ->  { _:Proof | deliverable m procVc }
    ->  DeliverablePropK m procVc
@-}
d_implies_dk :: VC -> Message r -> Proof -> (PID -> Proof)
d_implies_dk _vc _m _proof _pid
    =   () -- ? iterImpliesForall 
    *** Admit

{-@
cb_implies_cbk
    ::  m1 : Message r
    ->  m2 : Message r
    ->  { _:Proof | causallyBefore m1 m2 }
    ->  CausallyBeforePropK m1 m2
@-}
cb_implies_cbk :: Message r -> Message r -> Proof -> (PID -> Proof)
cb_implies_cbk _m1 _m2 _proof _pid = () *** Admit

{-@ ple safety @-}
{-@
safety
    ::  procVc : VC
    ->  m1 : Message r
    ->  m2 : Message r
    ->  { _:Proof | deliverable m1 procVc }
    ->  { _:Proof | causallyBefore m1 m2 }
    ->  { _:Proof | deliverable m2 procVc }
    ->  { _:Proof | false }
@-}
safety :: VC -> Message r -> Message r -> Proof -> Proof -> Proof -> Proof
safety procVc m1 m2 m1_d_p m1_before_m2 m2_d_p
    | mSender m1 == mSender m2
        =   ()
            ? (d_implies_dk procVc m1 m1_d_p) (mSender m1)
            ? (d_implies_dk procVc m2 m2_d_p) (mSender m2)
            ? processOrderAxiom m1 m2 ()
            *** QED
    | otherwise
        =   ()
            ? (cb_implies_cbk m1 m2 m1_before_m2) (mSender m1)
            ? (d_implies_dk procVc m1 m1_d_p) (mSender m1)
            ? (d_implies_dk procVc m2 m2_d_p) (mSender m1)
            *** QED
