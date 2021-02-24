-- | Attempt to translate the safety proof Gan did in agda to LiquidHaskell,
-- more or less exactly, but use more liquid-haskell native representations of
-- specs.
--
-- Status: Safety proof of spec passes (same as Verification8); Proving
-- implementation matches spec is in progress
module Causal.CBCAST.Verification8nGlobImpls where

import Prelude hiding (lookup)
import Language.Haskell.Liquid.ProofCombinators

-- $setup
-- >>> instance Show (a -> b) where show _ = "fun"


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

{-@ type DeliverableProp M P = k:Fin n -> { _:Proof | deliverableK M P k } @-}
type DeliverableProp = Fin -> Proof

{-@ reflect causallyBeforeK @-}
{-@
causallyBeforeK :: Message -> Message -> Fin n -> Bool @-}
causallyBeforeK :: Message -> Message -> Fin -> Bool
causallyBeforeK m1 m2 k
    =   bang (messageVc m1) k <= bang (messageVc m2) k
    &&  messageVc m1 /= messageVc m2

{-@ type CausallyBeforeProp M1 M2 = k:Fin n -> { _:Proof | causallyBeforeK M1 M2 k } @-}
type CausallyBeforeProp = Fin -> Proof

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
    ->  DeliverableProp m1 p
    ->  CausallyBeforeProp m1 m2
    ->  DeliverableProp m2 p
    ->  { _:Proof | false}
@-}
safety :: Process -> Message -> Message -> DeliverableProp -> CausallyBeforeProp -> DeliverableProp -> Proof
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


-- * Safety of impl

{-@ type MessageN = {m:Message | n == len (messageVc m)} @-}
{-@ type ProcessN = {p:Process | n == len (procVc p)} @-}

{-@ reflect deliverable @-}
{-@ deliverable :: MessageN -> ProcessN -> Bool @-}
deliverable :: Message -> Process -> Bool
deliverable msg proc
    = listFoldl boolAnd True
    . listMap (deliverableK msg proc)
    . fin . listLength . messageVc $ msg

{-@ reflect causallyBefore @-}
{-@ causallyBefore :: MessageN -> MessageN -> Bool @-}
causallyBefore :: Message -> Message -> Bool
causallyBefore m1 m2
    = listFoldl boolAnd True
    . listMap (causallyBeforeK m1 m2)
    . fin . listLength . messageVc $ m1

{-@ ple deliverableImpliedBySpec @-}
{-@
deliverableImpliedBySpec
    :: m:Message
    -> p:Process
    -> DeliverableProp m p
    -> { _:Proof | deliverable m p}
@-}
deliverableImpliedBySpec :: Message -> Process -> DeliverableProp -> Proof
deliverableImpliedBySpec _ _ _ = () *** Admit

{-@ ple deliverableImpliesSpec @-}
{-@
deliverableImpliesSpec
    :: m:Message
    -> p:Process
    -> { _:Proof | deliverable m p}
    -> DeliverableProp m p
@-}
deliverableImpliesSpec :: Message -> Process -> Proof -> DeliverableProp
deliverableImpliesSpec _ _ _ _ = () *** Admit

-- TODO: also proofs for causally-before



-- * Agda things reimplemented

{-@ type Vec a V = {v:[a] | len v == V} @-}
type Vec a = [a]

{-@ type Fin V = {v:Nat | v < V} @-}
type Fin = Int

-- | Generate the elements of a finite set @Fin n@. I don't know if this is a
-- thing in agda or not.
--
-- >>> fin (-1)
-- []
-- >>> fin 0
-- []
-- >>> fin 1
-- [0]
-- >>> fin 2
-- [1,0]
--
{-@ reflect fin @-}
{-@ fin :: v:Nat -> {xs:[{x:Nat | x < v}]<{\a b -> a > b}> | len xs == v} @-}
fin :: Int -> [Int]
fin k = let k' = k - 1 in if 0 < k then k' : fin k' else []

{-@ reflect lookup @-}
{-@ lookup :: xs:[a] -> {i:Nat | i < len xs } -> a @-}
lookup :: [a] -> Int -> a
lookup (x:xs) i
    | i == 0    = x
    | otherwise = lookup xs (i-1)


-- * Haskell things reimplemented

{-@ reflect boolAnd @-}
{-@ boolAnd :: a:Bool -> b:Bool -> {c:Bool | c <=> a && b} @-}
boolAnd :: Bool -> Bool -> Bool
boolAnd True True = True
boolAnd _ _ = False

-- | Reify the @len@ measure defined in the @liquid-base@ specification into
-- code and back into specifications.
--
-- prop> length xs == listLength xs
{-@
listLength :: xs:_ -> {n:Nat | n == len xs } @-}
listLength :: [a] -> Int
listLength [] = 0
listLength (_x:xs) = 1 + listLength xs
{-@ measure listLength @-}

-- | Implementation of 'map' lifted to specifications. Probably same as
-- 'Prelude'.
--
-- prop> map f xs == listMap f xs
{-@ reflect listMap @-}
listMap :: (a -> b) -> [a] -> [b]
listMap f (x:xs) = f x:listMap f xs
listMap _ [] = []

-- | Implementation of 'foldl' lifted to specifications. Probably same as
-- 'Prelude'.
--
-- prop> foldl f acc xs == listFoldl f acc xs
{-@ reflect listFoldl @-}
listFoldl :: (b -> a -> b) -> b -> [a] -> b
listFoldl f acc (x:xs) = listFoldl f (f acc x) xs
listFoldl _ acc [] = acc

-- | Implementation of 'impossible' lifted to specifications. similar to the
-- one in 'Language.Haskell.Liquid.ProofCombinators'.
{-@ inline impossibleConst @-}
{-@ impossibleConst :: a -> {v:b | false } -> a @-}
impossibleConst :: a -> b -> a
impossibleConst a _ = a
