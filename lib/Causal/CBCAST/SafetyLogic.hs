{-# OPTIONS_GHC "-Wno-unused-imports" #-} -- LH needs Redefined to be imported for specs
module Causal.CBCAST.SafetyLogic where

import Language.Haskell.Liquid.ProofCombinators

import Redefined
import Causal.CBCAST.VectorClock
import Causal.CBCAST.Message
import Causal.CBCAST.Process
import Causal.CBCAST.Protocol
import qualified Causal.CBCAST.DelayQueue -- LH breaks without this

-- | The @CausallyBeforeProp@ type makes use of the isomorphism
-- between the vector clock ordering and the happens-before relation.
{-@
type CausallyBeforeProp M1 M2
    =   k : PID
    ->  { _:Proof | vcReadK (mSent M1) k <= vcReadK (mSent M2) k
                 &&          mSent M1    /=          mSent M2    }
@-}
type CausallyBeforeProp = PID -> Proof

-- | The @DeliveredProp@ type says that a message has been delivered at a
-- process by checking the process's vector clock.  If the process VC
-- is at least as big as the message VC, the message has been
-- delivered.
{-@
type DeliveredProp M P
    =   k : PID
    ->  { _:Proof | vcLessEqualK (mSent M) P k }
@-}
type DeliveredProp = PID -> Proof

-- | The @DeliverableProp@ type says that a message is deliverable at a
-- process.  It is written terms of @deliverableK@.
{-@
type DeliverableProp M P
    =  k : PID
    -> { _:Proof | deliverableK M P k }
@-}
type DeliverableProp = PID -> Proof

-- | @iterImpliesForall@ lets us take a proof about a function that
-- iterates a predicate over all entries in a vector clock, and turns
-- it into a function that takes a vector clock index and returns a
-- proof that the predicate holds at that particular index.  This is
-- handy because it lets us turn a proof about the @deliverable@
-- function into a proof about @DeliverableProp@.
{-@ ple iterImpliesForall @-}
{-@
iterImpliesForall
    :: n : Nat
    -> p : (Fin {n} -> Bool)
    -> { _:Proof | iter n p }
    -> (k : Fin {n} -> { _:Proof | p k })
@-}
iterImpliesForall :: Int -> (Fin -> Bool) -> Proof -> (Fin -> Proof)
iterImpliesForall n p satisfied k
    -- Insight: boolAnd (p (n - 1)) (listFoldr boolAnd True (listMap p (fin (n - 1))))
    | k == n - 1 = ()
    | k <  n - 1 = iterImpliesForall (n - 1) p satisfied k

-- | @deliverableImpliesDeliverableProp@ converts a proof that a
-- message m is @deliverable@ at a process with VC procVC into a proof
-- that m is @DeliverableProp@ at a process with procVC.  The
-- difference is that @deliverable@ iterates over entries in a VC,
-- while @DeliverableProp@ uses universal quantification.  Converting
-- to the latter makes the proof easier for Liquid Haskell to carry
-- out.
{-@ ple deliverableImpliesDeliverableProp @-}
{-@
deliverableImpliesDeliverableProp
    ::  p: VC
    ->  m : Message r
    ->  { _:Proof | deliverable m p }
    ->  DeliverableProp m p
@-}
deliverableImpliesDeliverableProp :: VC -> Message r -> Proof -> DeliverableProp
deliverableImpliesDeliverableProp p m m_deliverable_p k =
    iterImpliesForall (vcSize (mSent m)) (deliverableK m p) m_deliverable_p k

-- | @vcAxiom@ encodes a standard observation about vector clocks: If
-- m1 -> m2, then VC(m1) will be strictly less than VC(m2) at the
-- index of m2's sender.
{-@
assume vcAxiom
    :: m1 : Message r
    -> m2 : Message r
    -> CausallyBeforeProp {m1} {m2}
    -> { _:Proof | vcReadK (mSent m1) (mSender m2) < vcReadK (mSent m2) (mSender m2) }
@-}
vcAxiom :: Message r -> Message r -> CausallyBeforeProp -> Proof
vcAxiom _m1 _m2 _m1_before_m2 = ()

{-@ ple deliveredPropImpliesDelivered @-}
{-@
assume deliveredPropImpliesDelivered
    :: p : Process r
    -> m : Message r
    -> DeliveredProp {m} {(pVC p)}
    -> { _:Proof | inDelivered p m }
@-}
deliveredPropImpliesDelivered :: Process r -> Message r -> DeliveredProp -> Proof
deliveredPropImpliesDelivered _p _m _dp = ()

{-@ ple causalSafety @-}
{-@
causalSafety
    :: p : Process r
    -> m1 : Message r
    -> m2 : Message r
    -> { _:Proof | deliverable m2 (pVC p) }
    -> CausallyBeforeProp {m1} {m2}
    -> { _:Proof | inDelivered p m1 }
@-}
causalSafety :: Process r -> Message r -> Message r -> Proof -> CausallyBeforeProp -> Proof
causalSafety p m1 m2 m2_deliverable_p m1_before_m2 =
  deliveredPropImpliesDelivered p m1 (causalSafetyInner (pVC p) m1 m2 m2_deliverable_p m1_before_m2)

-- | @causalSafety@ says that, given two messages m1 and m2 where m1
-- -> m2 and m2 is @deliverable@ at p, m1 has already been delivered
-- at p.
{-@ ple causalSafetyInner @-}
{-@
causalSafetyInner
    :: procVc : VC
    -> m1 : Message r
    -> m2 : Message r
    -> { _:Proof | deliverable m2 procVc }
    -> CausallyBeforeProp {m1} {m2}
    -> DeliveredProp {m1} {procVc}
@-}
causalSafetyInner :: VC -> Message r -> Message r -> Proof -> CausallyBeforeProp -> DeliveredProp
causalSafetyInner procVc m1 m2 m2_deliverable_p m1_before_m2 k
    | k /= mSender m2 = m1_before_m2 k
                        ? (deliverableImpliesDeliverableProp procVc m2 m2_deliverable_p) k
    | k == mSender m2 = m1_before_m2 k
                        ? (deliverableImpliesDeliverableProp procVc m2 m2_deliverable_p) k
                        ? vcAxiom m1 m2 m1_before_m2
                        *** QED                     
                           
