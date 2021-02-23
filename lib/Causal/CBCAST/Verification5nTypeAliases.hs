-- | Translate Gan's proof in agda to a LiquidHaskell-native approach
--
-- Parameterize over N via type aliases.
--
-- Status: Incomplete, proof doesn't work
module Causal.CBCAST.Verification5nTypeAliases where

import Prelude hiding (lookup)
import Language.Haskell.Liquid.ProofCombinators

{-@ type Pos = {n:Nat | 1 <= n} @-}

{-@ type VectorClockN N = Vec Nat N @-}
{-@ type VectorClock = [Nat] @-}
type VectorClock = [Int]

{-@ reflect bang @-}
{-@ bang :: vc:VectorClock -> Fin (len vc) -> Nat @-}
bang :: VectorClock -> Fin -> Int
bang vc k = lookup vc k

{-@
data Message = Message { mVcN :: Pos, senderId :: Fin mVcN, messageVc :: VectorClockN mVcN } @-}
data Message = Message { mVcN :: Int, senderId :: Fin     , messageVc :: VectorClock       }
{-@ type MessageN N = {m:Message | mVcN m == N} @-}

{-@
data Process = Process { pVcN :: Pos, procId :: Fin pVcN, procVc :: VectorClockN pVcN } @-}
data Process = Process { pVcN :: Int, procId :: Fin     , procVc :: VectorClock       }
{-@ type ProcessN N = {p:Process | pVcN p == N} @-}

-- | @iter f k@ calls @f@ on each value of the finite set @Fin n@ starting with
-- @k@ and combines the results with @&&@.
{-@ reflect iter @-}
{-@
iter :: n:Nat -> (Fin n -> Bool) -> k:Fin n -> Bool / [n - k] @-}
iter :: Int -> (Fin -> Bool) -> Fin -> Bool
iter n f k
    | k < n = f k && if k' < n then iter n f k' else True
    | otherwise = impossibleConst False "all cases covered"
  where
    k' = k + 1

{-@ reflect deliverable @-}
{-@
deliverable :: m:Message -> ProcessN (mVcN m) -> Bool @-}
deliverable :: Message -> Process -> Bool
deliverable msg proc = iter (mVcN msg) (deliverableK msg proc) 0

{-@ reflect deliverableK @-}
{-@
deliverableK :: m:Message -> ProcessN (mVcN m) -> Fin (mVcN m) -> Bool @-}
deliverableK :: Message -> Process -> Fin -> Bool
deliverableK msg proc k
    | k == senderId msg     = bang (messageVc msg) k == bang (procVc proc) k + 1
    | k /= senderId msg     = bang (messageVc msg) k <= bang (procVc proc) k
    | otherwise = impossibleConst False "all cases covered"

{-@ reflect causallyBefore @-}
{-@
causallyBefore :: m:Message -> MessageN (mVcN m) -> Bool @-}
causallyBefore :: Message -> Message -> Bool
causallyBefore m1 m2 = iter (mVcN m1) (causallyBeforeK m1 m2) 0

{-@ reflect causallyBeforeK @-}
{-@
causallyBeforeK :: m:Message -> MessageN (mVcN m) -> Fin (mVcN m) -> Bool @-}
causallyBeforeK :: Message -> Message -> Fin -> Bool
causallyBeforeK m1 m2 k
    =   bang (messageVc m1) k <= bang (messageVc m2) k
    &&  messageVc m1 /= messageVc m2

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
    -> {m2 : Message | senderId m1 == senderId m2}
    -> { bang (messageVc m1) (senderId m1) != bang (messageVc m2) (senderId m2) }
@-}
processOrderAxiom :: Message -> Message -> Proof
processOrderAxiom _m1 _m2 = ()

-- {-@ ple safety @-}
-- {-@
-- safety
--     ::  n : Nat
--     ->  p : ProcessN n
--     ->  {m1 : MessageN n | deliverable m1 p}
--     ->  {m2 : MessageN n | causallyBefore m1 m2}
--     ->  { not (deliverable m2 p) }
-- @-}
-- safety :: Int -> Process -> Message -> Message -> Proof
-- safety _n _p m1 m2
--     | senderId m1 == senderId m2 = processOrderAxiom m1 m2
--     | senderId m1 /= senderId m2 = () *** QED
--     | otherwise = impossibleConst () "all cases covered"


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
