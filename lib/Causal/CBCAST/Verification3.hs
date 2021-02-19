module Causal.CBCAST.Verification3 where

import Prelude hiding (lookup)
import Language.Haskell.Liquid.ProofCombinators

-- | The whole module is parameterized over the number of processes n
{-@ reflect n @-}
{-@ n :: Nat @-}
n :: Int
n = 4

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
    ->  ( { _:Proof | k == senderId MSG => bang (messageVc MSG) k == bang (procVc PROC) k + 1 }
        , { _:Proof | k /= senderId MSG => bang (messageVc MSG) k <= bang (procVc PROC) k     }
        )
@-}
type Deliverable = Fin -> (Proof, Proof)

{-@
type CausallyBefore M1 M2
    =   ( k : Fin n -> { _:Proof | bang (messageVc m1) k <= bang (messageVc m2) k }
        , { _:Proof | messageVc m1 /= messageVc m2 }
        )
@-}
type CausallyBefore = (Fin -> Proof, Proof)

{-@
causallyBeforeSameSender
    ::  m1 : Message
    ->  m2 : Message
    ->  CausallyBefore m1 m2
    ->  { _:Proof | senderId m1 == senderId m2 }
    ->  { _:Proof | bang (messageVc m1) (senderId m1) < bang (messageVc m2) (senderId m2) }
@-}
causallyBeforeSameSender :: Message -> Message -> CausallyBefore -> Proof -> Proof
causallyBeforeSameSender _m1 _m2 _m1_before_m2 _s1_eq_s2 = () *** Admit

{-@
safety
    ::  p : Process
    ->  m1 : Message
    ->  m2 : Message
    ->  Deliverable m1 p
    ->  CausallyBefore m1 m2
    ->  { v:Deliverable m2 p | True }
@-} -- FIXME: HOW TO NEGATE A TUPLE?
safety :: Process -> Message -> Message -> Deliverable -> CausallyBefore -> Deliverable
safety p m1 m2 m1_d_p m1_before_m2 k =
    ( ()
    , () *** Admit
    )


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
