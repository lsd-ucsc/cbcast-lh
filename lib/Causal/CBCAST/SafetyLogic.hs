{-# OPTIONS_GHC "-Wno-unused-imports" #-} -- LH needs Redefined to be imported for specs
module Causal.CBCAST.SafetyLogic where

import Language.Haskell.Liquid.ProofCombinators

import Redefined
import Causal.CBCAST.VectorClock
import Causal.CBCAST.Message

-- | The @CausallyBefore@ type makes use of the isomorphism between
-- the vector clock ordering and the happens-before relation.
{-@
type CausallyBefore M1 M2
    =   k : PID
    ->  { _:Proof | causallyBeforeK M1 M2 k }
@-}
type CausallyBefore = PID -> Proof

-- | The @DeliveredVC@ type says that a message has been delivered at a
-- process by checking the process's vector clock.  If the process VC
-- is at least as big as the message VC, the message has been
-- delivered.
{-@
type DeliveredVC M P
    =   k : PID
    ->  { _:Proof | vcLessEqualK (mSent M) P k }
@-}
type DeliveredVC = PID -> Proof

-- | The @Deliverable@ type says that a message is deliverable at a
-- process.  It is written terms of @deliverableK@.
{-@
type Deliverable M P
    =  k : PID
    -> { _:Proof | deliverableK M P k }
@-}
type Deliverable = PID -> Proof

-- | @iterImpliesForall@ lets us take a proof about a function that
-- iterates a predicate over all entries in a vector clock, and turns
-- it into a function that takes a vector clock index and returns a
-- proof that the predicate holds at that particular index.  This is
-- handy because it lets us turn a proof about the @deliverable@
-- function into a proof about @Deliverable@.
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

-- | @dImpliesD@ converts a proof that a message m is @deliverable@ at
-- a process with VC procVC into a proof that m is @Deliverable@ at a
-- process with procVC.  The difference is that @deliverable@ iterates
-- over entries in a VC, while @Deliverable@ uses universal
-- quantification.  Converting to the latter makes the proof easier
-- for Liquid Haskell to carry out.
{-@ ple dImpliesD @-}
{-@
dImpliesD
    ::  p: VC
    ->  m : Message r
    ->  { _:Proof | deliverable m p }
    ->  Deliverable m p
@-}
dImpliesD :: VC -> Message r -> Proof -> Deliverable
dImpliesD p m m_deliverable_p k =
    iterImpliesForall (vcSize (mSent m)) (deliverableK m p) m_deliverable_p k

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

{-@ ple cbImpliesCB@-}
{-@
cbImpliesCB
    ::  m1 : Message r
    ->  m2 : Message r
    ->  { _:Proof | causallyBefore m1 m2 }
    ->  CausallyBefore m1 m2
@-}
cbImpliesCB :: Message r -> Message r -> Proof -> CausallyBefore
cbImpliesCB m1 m2 m1_before_m2 k =
    iterImpliesForall (vcSize (mSent m1)) p m1_before_m2 k
  where
--  p = causallyBeforeK m1 m2
    p = vcLessK (mSent m1) (mSent m2) -- Why can't we use the commented p here?

-- | @vcAxiom@ encodes a standard observation about vector clocks: If
-- m1 -> m2, then VC(m1) will be strictly less than VC(m2) at the
-- index of m2's sender.
{-@
assume vcAxiom
    :: m1 : Message r
    -> m2 : Message r
    -> CausallyBefore {m1} {m2}
    -> { _:Proof | vcReadK (mSent m1) (mSender m2) < vcReadK (mSent m2) (mSender m2) }
@-}
vcAxiom :: Message r -> Message r -> CausallyBefore -> Proof
vcAxiom _m1 _m2 _m1_before_m2 = ()

-- | @causalSafety@ says that, given two messages m1 and m2 where m1
-- -> m2 and m2 is @deliverable@ at p, m1 has already been delivered
-- at p.
{-@ ple causalSafety @-}
{-@
causalSafety
    :: p : VC
    -> m1 : Message r
    -> m2 : Message r
    -> { _:Proof | deliverable m2 p }
    -> CausallyBefore {m1} {m2}
    -> Delivered {m1} {p}
@-}
causalSafety :: VC -> Message r -> Message r -> Proof -> CausallyBefore -> Delivered
causalSafety p m1 m2 m2_deliverable_p m1_before_m2 k
    | k /= mSender m2 = () ? m1_before_m2 k
                           ? (dImpliesD p m2 m2_deliverable_p) k
    | k == mSender m2 = () ? m1_before_m2 k
                           ? (dImpliesD p m2 m2_deliverable_p) k
                           ? vcAxiom m1 m2 m1_before_m2
                           *** QED                     
                           
