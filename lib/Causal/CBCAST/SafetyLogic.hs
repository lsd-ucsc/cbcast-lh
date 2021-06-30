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

-- | @distinctAtSenderM2@ says that, given two messages m1 and m2
-- where m1 -> m2, their VC entries are distinct in the position of
-- m2's sender.  (This is the case since in any execution that can
-- occur, if m1 -> m2, then m2's sender knows about m2's send at the
-- time it sends m2, but m1's sender cannot have known about m2's send
-- at the time it sends m1.  So m2 will have a VC with an entry in its
-- own sender's position that is, at a minimum, one larger than m1 in
-- the corresponding position, to account for its own send of m2.
-- However, we cannot prove this in our formalism because we haven't
-- formalized a notion of what executions can occur.)
{-@
assume distinctAtSenderM2
    :: m1 : Message r
    -> m2 : Message r
    -> CausallyBefore {m1} {m2}
    -> { _:Proof | vcReadK (mSent m1) (mSender m2) != vcReadK (mSent m2) (mSender m2) }
@-}
distinctAtSenderM2 :: Message r -> Message r -> CausallyBefore -> Proof
distinctAtSenderM2 _m1 _m2 _m1_before_m2 = ()

{-@ ple safety2 @-}
{-@
safety2
    :: p : VC
    -> m1 : Message r
    -> m2 : Message r
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
