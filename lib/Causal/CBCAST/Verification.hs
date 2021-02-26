{-# OPTIONS_GHC "-Wno-unused-imports" #-} -- LH needs Redefined to be imported for specs
-- | Implementation of vector clocks and safety proof for deliverability
-- predicate. Safety proof uses implementation components as part of the spec.
--
-- To follow the proof, start with VectorClock.hs, then Message.hs, then this
-- file.
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

-- | Property: The given property is false.
{-@
type Not t = t -> { _:Proof | false } @-}
type Not t = t -> Proof

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
--
-- Here's an explanation of what is going on in the proof.  Note that
-- `Not (DeliverableProp m2 p)` expands out to `DeliverableProp m2 p
-- -> { _:Proof | false }`.  `m2_d_p` is the proof that
-- `DeliverableProp m2 p`, which will let us prove false.
--
-- In the first case, if we apply the `DeliverableProp m1 p` function
-- to `mSender m1`, we see that `m1`'s VC entry in the sender position
-- is OK for deliverability, so it must be one greater than `p`'s VC
-- in the sender position.  Likewise, if we apply our `DeliverableProp
-- m2 p` function to `msender m2`, we see that `m2`'s VC entry in its
-- sender position (which is the same as `m1`'s sender) is OK for
-- deliverability, so it must also be one greater than `p`'s VC.  But
-- this is a contradiction, because `processOrderAxiom` says that
-- these entries in message from the same sender must be distinct, so
-- we're able to prove false, as needed.
--
-- In the second case, if we apply the `CausallyBeforeProp m1 m2`
-- function to `mSender m1` we see that `m1`'s VC is less than or
-- equal to `m2`'s VC in the position of `m1`'s sender, call it k.  We
-- also have that `m1` is deliverable, so applying the
-- `DeliverableProp m1 p` function to k, we see that `m1`'s VC entry
-- in the k-th position is OK for deliverability, so it must be one
-- greater than `p`'s VC in position k.  Applying the `DeliverableProp
-- m2 p` function to k, we see that `m2`'s VC entry in the k-th
-- position is OK for deliverability, so (since `m2` was not sent by
-- process k) its k-th entry must be less than or equal to `p`'s VC in
-- position k.
--
-- Putting together these facts about the k-th position (m1's sender's
-- position), we have:
--
--   - m1's VC[k] <= m2's VC[k]  (via causal order of m1 and m2)
--   - m1's VC[k] = (process VC[k]) + 1 (via deliverability of m1)
--   - m2's VC[k] <= process VC[k] (via deliverability of m2)
--
-- So:
--   m1's VC[k] <= m2's VC[k] <= process VC[k] <
--   (process VC[k]) + 1 = m1's VC[k]
--
-- which is a contradiction because we've just said that m1's VC in
-- position k is less than itself, letting us prove false, as needed.

{-@ ple safetyProof @-}
{-@
safetyProof
    ::  p : Proc
    ->  m1 : Message r
    ->  m2 : Message r
    ->  DeliverableProp m1 p
    ->  CausallyBeforeProp m1 m2
    ->  Not (DeliverableProp m2 p)
@-}


safetyProof :: Proc -> Message r -> Message r -> DeliverableProp -> CausallyBeforeProp -> Not (DeliverableProp)
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
