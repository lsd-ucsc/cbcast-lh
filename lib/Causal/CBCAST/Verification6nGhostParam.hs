-- | Translate Gan's proof in agda to a LiquidHaskell-native approach
--
-- Parameterize over N by adding a ghost-parameter everywhere.
--
-- Status: Incomplete, proof doesn't work
module Causal.CBCAST.Verification6nGhostParam where

import Prelude hiding (lookup)
import Language.Haskell.Liquid.ProofCombinators

{-@ type Pos = {n:Nat | 1 <= n} @-}

{-@ type VectorClockN N = Vec Nat N @-}
{-@ type VectorClock = [Nat] @-}
type VectorClock = [Int]

{-@ reflect bang @-}
{-@ bang :: n:Pos -> VectorClockN n -> Fin n -> Nat @-}
bang :: Int -> VectorClock -> Fin -> Int
bang _n vc k = lookup vc k

{-@
data Message = Message { messageVc :: VectorClock, senderId :: Fin (len messageVc) } @-}
data Message = Message { messageVc :: VectorClock, senderId :: Fin }
{-@ type MessageN N = {m:Message | len (messageVc m) == N && senderId m < N} @-}

{-@
data Process = Process { procVc :: VectorClock, procId :: Fin (len procVc)} @-}
data Process = Process { procVc :: VectorClock, procId :: Fin }
{-@ type ProcessN N = {p:Process | len (procVc p) == N && procId p < N} @-}

-- | @iter n f k@ calls @f@ on each value of the finite set @Fin n@ starting with
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
deliverable :: n:Pos -> MessageN n -> ProcessN n -> Bool @-}
deliverable :: Int -> Message -> Process -> Bool
deliverable n msg proc = iter n (deliverableK n msg proc) 0

{-@ reflect deliverableK @-}
{-@
deliverableK :: n:Pos -> MessageN n -> ProcessN n -> Fin n -> Bool @-}
deliverableK :: Int -> Message -> Process -> Fin -> Bool
deliverableK n msg proc k
    | k == senderId msg     = bang n (messageVc msg) k == bang n (procVc proc) k + 1
    | k /= senderId msg     = bang n (messageVc msg) k <= bang n (procVc proc) k
    | otherwise = impossibleConst False "all cases covered"

{-@ reflect causallyBefore @-}
{-@
causallyBefore :: n:Pos -> MessageN n -> MessageN n -> Bool @-}
causallyBefore :: Int -> Message -> Message -> Bool
causallyBefore n m1 m2 = iter n (causallyBeforeK n m1 m2) 0

{-@ reflect causallyBeforeK @-}
{-@
causallyBeforeK :: n:Pos -> MessageN n -> MessageN n -> Fin n -> Bool @-}
causallyBeforeK :: Int -> Message -> Message -> Fin -> Bool
causallyBeforeK n m1 m2 k
    =   bang n (messageVc m1) k <= bang n (messageVc m2) k
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
    ::  n : Pos
    ->  m1 : MessageN n
    -> {m2 : MessageN n | senderId m1 == senderId m2}
    -> { bang n (messageVc m1) (senderId m1) != bang n (messageVc m2) (senderId m2) }
@-}
processOrderAxiom :: Int -> Message -> Message -> Proof
processOrderAxiom _n _m1 _m2 = ()

-- {-@ ple safety @-}
-- {-@
-- safety
--     ::  n : Pos
--     ->  p : ProcessN n
--     ->  {m1 : MessageN n | deliverable n m1 p}
--     ->  {m2 : MessageN n | causallyBefore n m1 m2}
--     ->  { not (deliverable n m2 p) }
-- @-}
-- safety :: Int -> Process -> Message -> Message -> Proof
-- safety n _p m1 m2
--     | senderId m1 == senderId m2 = processOrderAxiom n m1 m2
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
