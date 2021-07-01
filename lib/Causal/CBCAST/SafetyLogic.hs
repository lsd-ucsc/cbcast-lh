{-# OPTIONS_GHC "-Wno-unused-imports" #-} -- LH needs Redefined to be imported for specs
module Causal.CBCAST.SafetyLogic where

import Language.Haskell.Liquid.ProofCombinators

import Redefined
import Causal.CBCAST.VectorClock
import Causal.CBCAST.Message

-- | @iterImpliesForall@ lets us take a proof about a function that
-- iterates a predicate over all entries in a vector clock, and turns
-- it into a function that takes a vector clock index and returns a
-- proof that the predicate holds at that particular index.  This is
-- handy because it lets us turn a proof about, for instance, the
-- @deliverable@ function into a proof about @deliverableK@ for a
-- given @k@.
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

{-@
type CausallyBefore M1 M2 = k:PID -> { _:Proof | causallyBeforeK M1 M2 k }
@-}
type CausallyBefore = PID -> Proof

{-@ ple cb_implies_CB @-}
{-@
cb_implies_CB
    ::  m1 : Message r
    ->  m2 : Message r
    ->  { _:Proof | causallyBefore m1 m2 }
    ->  CausallyBefore m1 m2
@-}
cb_implies_CB :: Message r -> Message r -> Proof -> CausallyBefore
cb_implies_CB m1 m2 causallyBeforeSatisfied pid =
    iterImpliesForall (vcSize (mSent m1)) p causallyBeforeSatisfied pid
  where
    p = vcLessK (mSent m1) (mSent m2)

{-@
type Delivered MSG PROCVC
    =   k : PID
    ->  { _:Proof | vcReadK (mSent MSG) k <= vcReadK PROCVC k }
@-}
type Delivered = PID -> Proof

{-@
type Deliverable M P = k:PID -> { _:Proof | deliverableK M P k }
@-}
type Deliverable = PID -> Proof

{-@ ple d_implies_D @-}
{-@
d_implies_D
    ::  procVc: VC
    ->  m : Message r
    ->  { _:Proof | deliverable m procVc }
    ->  Deliverable m procVc
@-}
d_implies_D :: VC -> Message r -> Proof -> Deliverable
d_implies_D procVc m deliverableSatisfied pid =
    iterImpliesForall (vcSize (mSent m)) (deliverableK m procVc) deliverableSatisfied pid

-- | Axiom: for every message m, there exists some vector clock
-- procVcPrev such that m's vector clock is equal to procVcPrev but
-- incremented in the sender's position.  (procVcPrev can be thought
-- of as m's sender's VC right before being incremented for m's
-- sending.)
{-@
assume vcPrevWithProof
    :: m : Message r
    -> (procVcPrev :: VC,
        { _:Proof | mSent m == vcTick (mSender m) procVcPrev &&
                    vcReadK procVcPrev (mSender m) < vcReadK (mSent m) (mSender m) })
@-}
vcPrevWithProof :: Message r -> (VC, Proof)
vcPrevWithProof m = (vcBackTick (mSender m) (mSent m), ())
-- TODO: Maaaaybe this wouldn't have to be an axiom if we could prove that
-- vcTick (mSender m) (vcBackTick (mSender m) (mSent m)) == mSent m

{-@ reflect vcPrev @-}
{-@
assume vcPrev
    :: m : Message r
    -> { procVcPrev : VC | mSent m == vcTick (mSender m) procVcPrev &&
                           vcReadK procVcPrev (mSender m) < vcReadK (mSent m) (mSender m) }
@-}
vcPrev :: Message r -> VC
vcPrev m = (vcBackTick (mSender m) (mSent m))

-- TODO: could we use the above assumptions to prove vcInBetween?

-- | @vcInBetween@ says that, if we have two messages m1 and m2 with
-- distinct senders such that m1 -> m2, then there is some vector
-- clock value, procVCPrev, that is less than or equal to m1's VC in
-- sender(m2)'s position, and less than m2's VC in sender(m2)'s
-- position.
-- 
-- This is the case since in any execution that can occur, if m1 ->
-- m2, then m2's sender knows about m2's send at the time it sends m2,
-- but m1's sender cannot have known about m2's send at the time it
-- sends m1.  So m2 will have a VC with an entry in its own sender's
-- position that is, at a minimum, one larger than m1 in the
-- corresponding position, to account for its own send of m2.)
{-@
assume vcInBetween
    :: m1 : Message r
    -> { m2 : Message r | mSender m1 /= mSender m2 }
    -> CausallyBefore {m1} {m2}
    -> (procVcPrev :: VC,
        { _:Proof | vcReadK (mSent m1) (mSender m2) <= vcReadK procVcPrev (mSender m2) &&
                    vcReadK procVcPrev (mSender m2) <  vcReadK (mSent m2) (mSender m2) })
@-}
vcInBetween :: Message r -> Message r -> CausallyBefore -> (VC, Proof)
vcInBetween _m1 _m2 _m1_before_m2 = (vcPrev m2, ())

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
    ->  { m2 : Message r | m1 /= m2 }
    ->  { _:Proof | mSender m1 == mSender m2 }
    ->  { _:Proof | vcReadK (mSent m1) (mSender m1) != vcReadK (mSent m2) (mSender m2) }
@-}
processOrderAxiom :: Message r -> Message r -> Proof -> Proof
processOrderAxiom _m1 _m2 _proof = ()

-- | @distinctAtSenderM2@ says that, given two distinct messages m1
-- and m2 where m1 -> m2, their VC entries are distinct in the
-- position of m2's sender.
{-@
distinctAtSenderM2
    :: m1 : Message r
    -> { m2 : Message r | m1 /= m2 }
    -> CausallyBefore {m1} {m2}
    -> { _:Proof | vcReadK (mSent m1) (mSender m2) != vcReadK (mSent m2) (mSender m2) }
@-}
distinctAtSenderM2 :: Message r -> Message r -> CausallyBefore -> Proof
distinctAtSenderM2 m1 m2 m1_before_m2
    | mSender m1 == mSender m2 = () ? processOrderAxiom m1 m2 ()
    | mSender m1 /= mSender m2 = case (vcInBetween m1 m2 m1_before_m2) of
        (_, proof) -> proof

-- | @safety2@ says that, given two distinct messages m1 and m2 where
-- m1 -> m2 and m2 is deliverable at p, m1 has already been delivered
-- at p.
{-@ ple safety2 @-}
{-@
safety2
    :: p : VC
    -> m1 : Message r
    -> { m2 : Message r | m1 /= m2 }
    -> { _:Proof | deliverable m2 p }
    -> { _:Proof | causallyBefore m1 m2 }
    -> Delivered {m1} {p}
@-}
safety2 :: VC -> Message r -> Message r -> Proof -> Proof -> Delivered
safety2 p m1 m2 m2_deliverable_p m1_before_m2 k
    | k /= mSender m2 = () ? (cb_implies_CB m1 m2 m1_before_m2) k
                           ? (d_implies_D p m2 m2_deliverable_p) k
    | k == mSender m2 = () ? (cb_implies_CB m1 m2 m1_before_m2) k
                           ? (d_implies_D p m2 m2_deliverable_p) k
                           ? distinctAtSenderM2 m1 m2 (cb_implies_CB m1 m2 m1_before_m2)
                           *** QED                                        
