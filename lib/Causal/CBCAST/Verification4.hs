module Causal.CBCAST.Verification4 where

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

{-@ reflect iter @-}
{-@
iter :: (Fin n -> Bool) -> Fin n -> Bool @-}
iter :: (Fin -> Bool) -> Fin -> Bool
iter f k
    | k < n = f k && if k' < n then iter f k' else True
    | otherwise = impossibleConst False "all cases covered"
  where
    k' = k + 1

{-@ reflect deliverable @-}
{-@
deliverable :: Message -> Process -> Bool @-}
deliverable :: Message -> Process -> Bool
deliverable msg proc = iter (deliverableK msg proc) 0

{-@ reflect deliverableK @-}
{-@
deliverableK :: Message -> Process -> Fin n -> Bool @-}
deliverableK :: Message -> Process -> Fin -> Bool
deliverableK msg proc k
    | k == senderId msg     = bang (messageVc msg) k == bang (procVc proc) k + 1
    | k /= senderId msg     = bang (messageVc msg) k <= bang (procVc proc) k
    | otherwise = impossibleConst False "all cases covered"

{-@ reflect causallyBefore @-}
{-@
causallyBefore :: Message -> Message -> Bool @-}
causallyBefore m1 m2 = iter (causallyBeforeK m1 m2) 0

{-@ reflect causallyBeforeK @-}
{-@
causallyBeforeK :: Message -> Message -> Fin n -> Bool @-}
causallyBeforeK :: Message -> Message -> Fin -> Bool
causallyBeforeK m1 m2 k
    =   bang (messageVc m1) k <= bang (messageVc m2) k
    &&  messageVc m1 /= messageVc m2

{-@
causallyBeforeSameSender
    ::  m1 : Message
    ->  {m2 : Message | senderId m1 == senderId m2 && causallyBefore m1 m2 }
    ->  { bang (messageVc m1) (senderId m1) < bang (messageVc m2) (senderId m2) }
@-}
causallyBeforeSameSender :: Message -> Message -> Proof
causallyBeforeSameSender _m1 _m2 = () *** Admit

{-@ ple safety @-}
{-@
safety
    ::  p : Process
    ->  {m1 : Message | deliverable m1 p}
    ->  {m2 : Message | causallyBefore m1 m2}
    ->  { not (deliverable m2 p) }
@-}
safety :: Process -> Message -> Message -> Proof
safety p m1 m2
    | sender1 == sender2 =
        ( bang vc1 sender1 < bang vc2 sender2
            ? causallyBeforeSameSender m1 m2
            === True
        , deliverable m1 p
            === iter (deliverableK m1 p) 0
                ? assert (n > 0)
--          === (deliverableK m1 p 0 && if 1 < n then deliverableK m1 p 1 else True)
--          === bang vc1 sender1 == bang vcP sender1 + 1
--          === True
--          ? deliverable m1 p

--      , bang vc2 sender2 == bang vcP sender2 + 1
--          === True
--      , bang vc1 sender1 == 
        ) *** Admit
    | sender1 /= sender2 =
        () *** Admit
    | otherwise =
        impossibleConst () "all cases covered"
  where
    vc1 = messageVc m1
    vc2 = messageVc m2
    sender1 = senderId m1
    sender2 = senderId m2
    vcP = procVc p


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