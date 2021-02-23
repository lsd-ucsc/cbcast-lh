-- | Attempt to translate the things Gan did in agda to LiquidHaskell, more or
-- less exactly
--
-- Still has a global n. We will show that the proof time doesn't depend on the
-- global n (or use niki's trick to make the proof not aware of the concrete
-- n).
--
-- Status: Translated from agda with Gan. It works.
module Causal.CBCAST.Verification7nGlobSpecs where

import Prelude hiding (lookup)
import Language.Haskell.Liquid.ProofCombinators

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

{-@
type Deliverable MSG PROC
    =   k : Fin n
    ->  { _:Proof | ( k == senderId MSG => bang (messageVc MSG) k == bang (procVc PROC) k + 1 )
                 && ( k /= senderId MSG => bang (messageVc MSG) k <= bang (procVc PROC) k     )
        }
@-}
type Deliverable = Fin -> Proof

{-@
type CausallyBefore M1 M2
    =   k : Fin n
    ->  { _:Proof | (bang (messageVc m1) k <= bang (messageVc m2) k)
                 && (      messageVc m1    /=       messageVc m2   )
        }
@-}
type CausallyBefore = Fin -> Proof

{-@
assume causallyBeforeSameSender
    ::  m1 : Message
    ->  m2 : Message
    ->  CausallyBefore m1 m2
    ->  { _:Proof | senderId m1 == senderId m2 }
    ->  { _:Proof | bang (messageVc m1) (senderId m1) < bang (messageVc m2) (senderId m2) }
@-}
causallyBeforeSameSender :: Message -> Message -> CausallyBefore -> Proof -> Proof
causallyBeforeSameSender _m1 _m2 _proof () = ()

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
            ? causallyBeforeSameSender m1 m2 m1_before_m2 ()
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
