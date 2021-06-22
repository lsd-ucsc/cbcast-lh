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
--  | k == mSender m2 = () ? m1_before_m2 k ? m2_deliverable_p k ? lemma1 m1 m2 k m1_before_m2 ()
    | k == mSender m2 =
        if k == mSender m1
        then () ? m1_before_m2 k ? m2_deliverable_p k ? processOrderAxiom m1 m2 ()
        else () *** Admit
            -- m2 is from k
            -- m1 is NOT from k
            -- m1 is before m2 (less-equal and not-equal)

            -- Gan: we already know it's <=, all we need to prove is that it's /=; is
            -- there a contradiction from being ==?

            -- k == 0
            -- m1 1 [1,1,0]
            -- m2 0 [1,1,1]
            --
    -- KNOWLEDGE
    --
    -- k -> ( k == mSender m2 => vcReadK (mSent m2) k == vcReadK p k + 1 )
    --   && ( k /= mSender m2 => vcReadK (mSent m2) k <= vcReadK p k     )
    --
    -- k -> ( vcReadK (mSent m1) k <= vcReadK (mSent m2) k )
    --   && (          mSent m1    /=          mSent m2    )
    --
    -- GOAL
    --
    --                           vcReadK (mSent m1) k <= vcReadK p k

{-@
lemma1
    :: m1 : Message r
    -> m2 : Message r
    -> k : PID
    -> CausallyBefore {m1} {m2}
    -> { _:Proof | k == mSender m2 }
    -> { _:Proof | vcReadK (mSent m1) k < vcReadK (mSent m2) k }
@-}
lemma1 :: Message r -> Message r -> PID -> CausallyBefore -> Proof -> Proof
lemma1 m1 m2 k m1_before_m2 k_sent_m2
    | mSender m1 == mSender m2 = () ? m1_before_m2 k ? processOrderAxiom m1 m2 ()
    | mSender m1 /= mSender m2 = () *** Admit
    -- m1 is from ?
    -- m2 is from k
    -- m1 is before m2 (less-equal and not-equal)
    -- Gan: we already know it's <=, all we need to prove is that it's /=; is
    -- there a contradiction from being ==?

    -- k == 0
    -- m1 1 [0,1,0] (less-equal and not-equal)
    -- m2 0 [1,1,0]
