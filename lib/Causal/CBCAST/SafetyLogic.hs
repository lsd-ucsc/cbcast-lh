{-# OPTIONS_GHC "-Wno-unused-imports" #-} -- LH needs Redefined to be imported for specs
-- | Attempt to translate the things Gan did in agda to LiquidHaskell, more or
-- less exactly
module Causal.CBCAST.SafetyLogic where

import Language.Haskell.Liquid.ProofCombinators

import Redefined
import Causal.CBCAST.VectorClock
import Causal.CBCAST.Message

{-@
type CausallyBefore M1 M2
    =   k : PID
    ->  { _:Proof | ( vcReadK (mSent M1) k <= vcReadK (mSent M2) k )
                 && (          mSent M1    /=          mSent M2    )
        }
@-}
type CausallyBefore = Fin -> Proof
-- TODO: write in terms of VCLess rather than rewriting its definition here

{-@
type Delivered MSG PROCVC
    =   k : PID
    ->  { _:Proof | vcReadK (mSent MSG) k <= vcReadK PROCVC k
        }
@-}
type Delivered = Fin -> Proof

{-@
type Deliverable MSG PROCVC
    =   k : PID
    ->  { _:Proof | ( k == mSender MSG => vcReadK (mSent MSG) k == vcReadK PROCVC k + 1 )
                 && ( k /= mSender MSG => vcReadK (mSent MSG) k <= vcReadK PROCVC k     )
        }
@-}
type Deliverable = Fin -> Proof

-- | @processOrderAxiom@ says that every message sent by a given process has a
-- unique VC value at the sender position. (This follows from the fact that
-- events on a process have a total order.) This is enough to prove safety in
-- the same-sender case, because we already know that m1 -> m2, so we know that
-- for each position i in their respective VCs, VC(m1)[i] <= VC(m2)[i]. This
-- axiom rules out the case where they're equal, so then we know that VC(m1)[i]
-- < VC(m2)[i], which is the fact that LH needs to complete the proof.
{-@
assume processOrderAxiom
    ::    m1 : Message r
    ->  { m2 : Message r | m1 != m2 }
    ->  { _:Proof | mSender m1 == mSender m2 }
    ->  { _:Proof | vcReadK (mSent m1) (mSender m1) != vcReadK (mSent m2) (mSender m2) }
@-}
processOrderAxiom :: Message r -> Message r -> Proof -> Proof
processOrderAxiom _m1 _m2 _proof = ()

{-@ ple safety2 @-}
{-@
safety2
    :: p : VC
    -> m1 : Message r
    -> m2 : Message r
    -> Deliverable {m2} {p}
    -> CausallyBefore {m1} {m2}
    -> Delivered {m1} {p}
@-}
safety2 :: VC -> Message r -> Message r -> Deliverable -> CausallyBefore -> Delivered
safety2 p m1 m2 m2_deliverable_p m1_before_m2 k
    | k /= mSender m2 = () ? m1_before_m2 k ? m2_deliverable_p k
    | k == mSender m2 =
        if k == mSender m1
        then () ? m1_before_m2 k ? m2_deliverable_p k ? processOrderAxiom m1 m2 ()
        else () ? relateM1P k p m1 m2
                            (vc_m1_k_lt_vc_m2_k k p m1 m2)
                            (vc_m2_k_equals_vc_p_k_plus_1 k p m2 m2_deliverable_p) *** QED
        --else () ? m1_before_m2 k ? m2_deliverable_p k ? intermediateDelivery m1 m2 m1_before_m2 k ? vcSmallerAtIntermediateDelivery m2 k *** Admit


-- | Since sender(m1) /= sender(m2) and m1 -> m2, m1 must have been
-- delivered at sender(m2) before m2 was sent by sender(m2).  In fact,
-- by the step just *before* sender(m2)'s VC gets incremented in its
-- own position for sending m2, m1 must have already been delivered at
-- sender(m2).  That's what this lemma says.
{-@ ple intermediateDelivery @-}
{-@
intermediateDelivery
    :: m1 : Message r
    -> { m2 : Message r | mSender m1 /= mSender m2 }
    -> CausallyBefore {m1} {m2}
    -> Delivered {m1} (vcBackTick (mSender m2) (mSent m2))
@-}
intermediateDelivery :: Message r -> Message r -> CausallyBefore -> Delivered
intermediateDelivery m1 m2 m1_before_m2 k = () *** Admit

-- At some point after this intermediate delivery takes place on
-- sender(m2), m2 is sent.  We know that when m2 is sent, sender(m2)
-- increments its own position first, so the VC must have been
-- strictly smaller in the sender(m2) position at the intermediate
-- delivery time than it is in m2's VC.

-- | Another fact we need.
{-@ ple vcSmallerAtIntermediateDelivery @-}
{-@
vcSmallerAtIntermediateDelivery
    :: m : Message r
    -> k : PID
    -> { _:Proof | vcLessK (vcBackTick k (mSent m)) (mSent m) k }
@-}
vcSmallerAtIntermediateDelivery :: Message r -> PID -> Proof
vcSmallerAtIntermediateDelivery m k = () *** Admit

-- | NEED TO PROVE THIS
{-@ ple vc_m1_k_lt_vc_m2_k @-}
{-@
assume vc_m1_k_lt_vc_m2_k
    :: k : PID
    -> p : VC
    -> m1 : Message r
    -> m2 : Message r
    -> { _:Proof | vcReadK (mSent m1) k < vcReadK (mSent m2) k }
@-}
vc_m1_k_lt_vc_m2_k :: PID -> VC -> Message r -> Message r -> Proof
vc_m1_k_lt_vc_m2_k _k _p _m1 _m2 = ()

-- | Since we have deliverable(m2, p), we have VC(m2)[k] = VC(p)[k]+1
-- for k = sender(m2).
{-@ ple vc_m2_k_equals_vc_p_k_plus_1 @-}
{-@
vc_m2_k_equals_vc_p_k_plus_1
    :: k : PID
    -> p : VC
    -> { m2 : Message r | mSender m2 == k }
    -> Deliverable {m2} {p}
    -> { _:Proof | vcReadK (mSent m2) k == (vcReadK p k) + 1 }
@-}
vc_m2_k_equals_vc_p_k_plus_1 :: PID -> VC -> Message r -> Deliverable -> Proof
vc_m2_k_equals_vc_p_k_plus_1 k _p _m2 m2_deliverable_p = () ? m2_deliverable_p k *** QED

-- | If VC(m1)[k] < VC(m2)[k], and VC(m2)[k] = VC(p)[k]+1, then
-- VC(m1)[k] < VC(p)[k]+1.
{-@ ple relateM1P @-}
{-@
relateM1P
    :: k : PID
    -> p : VC
    -> m1 : Message r
    -> m2 : Message r
    -> { _:Proof | vcReadK (mSent m1) k < vcReadK (mSent m2) k }
    -> { _:Proof | vcReadK (mSent m2) k == (vcReadK p k) + 1 }
    -> { _:Proof | vcReadK (mSent m1) k < (vcReadK p k) + 1 }
@-}
relateM1P :: PID -> VC -> Message r -> Message r -> Proof -> Proof -> Proof
relateM1P _k _p _m1 _m2 _m1_lt_m2 _m2_eq_p_plus1 = ()
