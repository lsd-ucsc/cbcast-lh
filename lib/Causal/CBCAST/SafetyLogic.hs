{-# OPTIONS_GHC "-Wno-unused-imports" #-} -- LH needs Redefined to be imported for specs
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

-- | @distinctAtSenderM2@ says that, given two messages m1 and m2
-- where m1 -> m2, their VC entries are distinct in the position of
-- m2's sender.  (This is the case since in any execution that can
-- occur, if m1 -> m2, then m2's sender knows about m1's send, but
-- m1's sender cannot have known about m2's send.  So m2 will have a
-- VC with an entry in its own sender's position that is, at a
-- minimum, one larger than m1 in the corresponding position, to
-- account for its own send.  However, we cannot prove this in our
-- formalism because we haven't formalized a notion of what executions
-- can occur.)
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
    -> Deliverable {m2} {p}
    -> CausallyBefore {m1} {m2}
    -> Delivered {m1} {p}
@-}
safety2 :: VC -> Message r -> Message r -> Deliverable -> CausallyBefore -> Delivered
safety2 p m1 m2 m2_deliverable_p m1_before_m2 k
    | k /= mSender m2 = () ? m1_before_m2 k ? m2_deliverable_p k
    | k == mSender m2 =
        if k == mSender m1
        then () ? m1_before_m2 k ? m2_deliverable_p k ? distinctAtSenderM2 m1 m2 m1_before_m2
        -- Case where k /= mSender m1
        else () ? vc_m1_k_eq_vc_p_k_plus_1
                   k p m1 m2
                   (vc_m1_k_lt_vc_m2_k k m1 m2 m1_before_m2)
                   (vc_m2_k_equals_vc_p_k_plus_1 k p m2 m2_deliverable_p) *** QED

-- | VC(m1)[k] < VC(m2)[k] since m1 -> m2, so all entries are <=, and
-- since they have to be distinct at m2's sender's position, which is
-- k.
{-@ ple vc_m1_k_lt_vc_m2_k @-}
{-@
vc_m1_k_lt_vc_m2_k
    :: k : PID
    -> m1 : Message r
    -> { m2 : Message r | mSender m2 == k && mSender m1 /= mSender m2 }
    -> CausallyBefore {m1} {m2}
    -> { _:Proof | vcReadK (mSent m1) k < vcReadK (mSent m2) k }
@-}
vc_m1_k_lt_vc_m2_k :: PID -> Message r -> Message r -> CausallyBefore -> Proof
vc_m1_k_lt_vc_m2_k k m1 m2 m1_before_m2 =
  () ? m1_before_m2 k ? distinctAtSenderM2 m1 m2 m1_before_m2 *** QED

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
{-@ ple vc_m1_k_eq_vc_p_k_plus_1 @-}
{-@
vc_m1_k_eq_vc_p_k_plus_1
    :: k : PID
    -> p : VC
    -> m1 : Message r
    -> m2 : Message r
    -> { _:Proof | vcReadK (mSent m1) k < vcReadK (mSent m2) k }
    -> { _:Proof | vcReadK (mSent m2) k == (vcReadK p k) + 1 }
    -> { _:Proof | vcReadK (mSent m1) k < (vcReadK p k) + 1 }
@-}
vc_m1_k_eq_vc_p_k_plus_1 :: PID -> VC -> Message r -> Message r -> Proof -> Proof -> Proof
vc_m1_k_eq_vc_p_k_plus_1 _k _p _m1 _m2 _m1_lt_m2 _m2_eq_p_plus1 = () *** QED
