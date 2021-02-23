-- | Attempt to translate the things Gan did in agda to LiquidHaskell, more or
-- less exactly, but use more liquid-haskell native representations of specs.
--
-- Status: Works. It's very similar to Verification7nGlobSpecs.hs
module Causal.CBCAST.Verification8nGlobImpls where

import Prelude hiding (lookup)
import Language.Haskell.Liquid.ProofCombinators


-- * Safety of spec

-- | The LH specs are parameterized over n, but no value is given.
{-@ measure n :: Nat @-}

{-@ type VectorClock = Vec Nat n @-}
type VectorClock = [Int]

{-@ reflect bang @-}
{-@ bang :: VectorClock -> Fin n -> Nat @-}
bang :: VectorClock -> Fin -> Int
bang vc k = lookup vc k

{-@
data Message = Message { senderId :: Fin n, messageVc :: VectorClock } @-}
data Message = Message { senderId :: Fin  , messageVc :: VectorClock }

{-@
data Process = Process { procId :: Fin n, procVc :: VectorClock } @-}
data Process = Process { procId :: Fin  , procVc :: VectorClock }

{-@ reflect deliverableK @-}
{-@
deliverableK :: Message -> Process -> Fin n -> Bool @-}
deliverableK :: Message -> Process -> Fin -> Bool
deliverableK msg proc k
    | k == senderId msg     = bang (messageVc msg) k == bang (procVc proc) k + 1
    | k /= senderId msg     = bang (messageVc msg) k <= bang (procVc proc) k
    | otherwise = impossibleConst False "all cases covered"

{-@ type Deliverable M P = k:Fin n -> { _:Proof | deliverableK M P k } @-}
type Deliverable = Fin -> Proof

{-@ reflect causallyBeforeK @-}
{-@
causallyBeforeK :: Message -> Message -> Fin n -> Bool @-}
causallyBeforeK :: Message -> Message -> Fin -> Bool
causallyBeforeK m1 m2 k
    =   bang (messageVc m1) k <= bang (messageVc m2) k
    &&  messageVc m1 /= messageVc m2

{-@ type CausallyBefore M1 M2 = k:Fin n -> { _:Proof | causallyBeforeK M1 M2 k } @-}
type CausallyBefore = Fin -> Proof

-- | @processOrderAxiom@ says that every message sent by a given
-- process has a unique VC value at the sender position.  (This
-- follows from the fact that events on a process have a total order.)
-- This is enough to prove safety in the same-sender case, because we
-- already know that m1 -> m2, so we know that for each position i in
-- their respective VCs, VC(m1)[i] <= VC(m2)[i].  This axiom rules out
-- the case where they're equal, so then we know that VC(m1)[i] <
-- VC(m2)[i], which is the fact that LH needs to complete the proof.
{-@
assume processOrderAxiom
    ::  m1 : Message
    ->  m2 : Message
    ->  { _:Proof | senderId m1 == senderId m2 }
    ->  { _:Proof | bang (messageVc m1) (senderId m1) != bang (messageVc m2) (senderId m2) }
@-}
processOrderAxiom :: Message -> Message -> Proof -> Proof
processOrderAxiom _m1 _m2 _proof = ()

{-@ ple safety @-}
{-@
safety
    ::  p : Process
    ->  m1 : Message
    ->  m2 : Message
    ->  Deliverable m1 p
    ->  CausallyBefore m1 m2
    ->  Deliverable m2 p
    ->  { _:Proof | false}
@-}
safety :: Process -> Message -> Message -> Deliverable -> CausallyBefore -> Deliverable -> Proof
safety _p m1 m2 m1_d_p m1_before_m2 m2_d_p
    | senderId m1 == senderId m2
        =   ()
            ? m1_d_p (senderId m1)
            ? m2_d_p (senderId m2)
            ? processOrderAxiom m1 m2 ()
            *** QED
    | otherwise
        =   ()
            ? m1_before_m2 (senderId m1)
            ? m1_d_p (senderId m1)
            ? m2_d_p (senderId m1)
            *** QED


-- * Agda things reimplemented

{-@ type Vec a V = {v:[a] | len v == V} @-}
type Vec a = [a]

{-@ type Fin V = {v:Nat | v < V} @-}
type Fin = Int

{-@ reflect lookup @-}
{-@ lookup :: xs:[a] -> {i:Nat | i < len xs } -> a @-}
lookup :: [a] -> Int -> a
lookup (x:xs) i
    | i == 0    = x
    | otherwise = lookup xs (i-1)

-- | Implementation of 'impossible' lifted to specifications. similar to the
-- one in 'Language.Haskell.Liquid.ProofCombinators'.
{-@ inline impossibleConst @-}
{-@ impossibleConst :: a -> {v:b | false } -> a @-}
impossibleConst :: a -> b -> a
impossibleConst a _ = a
