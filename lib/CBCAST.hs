{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-} -- Must use "forall" to introduce them
{-# LANGUAGE TypeFamilies #-} -- For ~ constraint
{-# LANGUAGE StandaloneDeriving #-} -- Show instances of internal CBCAST types

-- | External CBCAST client functions which have no LH annotations.
module CBCAST where

import Data.Proxy (Proxy(..))
import GHC.TypeLits (Nat, KnownNat, natVal, CmpNat)
import Data.Bifunctor (bimap)
import Control.Applicative (Alternative)
import Control.Monad (guard)

import qualified VectorClock as V
import qualified CBCAST.Core as C
import qualified CBCAST.Transitions
import qualified CBCAST.Step as S

deriving instance Show r => Show (C.Process r)
deriving instance Show r => Show (C.Message r)
deriving instance Show r => Show (C.Event r)

-- | CBCAST Process indexed by a phantom Nat describing its VC size.
newtype Process (n :: Nat) r = Process (C.Process r)
    deriving Show

-- | CBCAST Message indexed by a phantom Nat describing its VC size.
newtype Message (n :: Nat) r = Message (C.Message r)
    deriving Show

newProcess
    :: forall pid n r. (KnownNat pid, KnownNat n, CmpNat pid n ~ 'LT)
    => Proxy pid -> Process n r
newProcess pidProxy
    | 0 <= pid && pid < n = Process $ C.pEmpty n pid
    | otherwise = undefined -- Impossible case
  where
    n = fromIntegral $ natVal (Proxy :: Proxy n)
    pid = fromIntegral $ natVal pidProxy

receive
    :: forall n r. KnownNat n
    => Message n r -> Process n r -> Process n r
receive (Message m) (Process p)
    -- FIXME: calls to vcSize
    | 0 <= n
    && n == V.vcSize (C.pVC p)
    && n == V.vcSize (C.mVC m) =
        let S.ResultReceive _n ret = S.step (S.OpReceive n m) p
        in Process ret
    | otherwise = undefined -- Impossible case (assuming deserialization of Process & Message correctly populate n::Nat phantom)
  where
    n = fromIntegral $ natVal (Proxy :: Proxy n)

deliver
    :: forall n r. KnownNat n
    => Process n r -> Maybe (Message n r, Process n r)
deliver (Process p)
    -- FIXME: calls to vcSize
    | 0 <= n
    && n == V.vcSize (C.pVC p) =
        let S.ResultDeliver _n ret = S.step (S.OpDeliver n) p
        in fmap (bimap Message Process) ret
    | otherwise = undefined -- Impossible case (assuming deserialization of Process & Message correctly populate n::Nat phantom)
  where
    n = fromIntegral $ natVal (Proxy :: Proxy n)

broadcast
    :: forall n r. KnownNat n
    => r -> Process n r -> (Message n r, Process n r)
broadcast raw (Process p)
    -- FIXME: calls to vcSize
    | 0 <= n
    && n == V.vcSize (C.pVC p) =
        let S.ResultBroadcast _n ret = S.step (S.OpBroadcast n raw) p
        in bimap Message Process ret
    | otherwise = undefined -- Impossible case (assuming deserialization of Process & Message correctly populate n::Nat phantom)
  where
    n = fromIntegral $ natVal (Proxy :: Proxy n)




-- | Helper for deserialization parser monads which will fail when the
-- process's VC size does not match the type.
guardProcess
    :: forall f n r. (Monad f, Alternative f, KnownNat n)
    => f (Process n r) -> f (Process n r)
guardProcess f = do
    Process m <- f
    guard (n == C.processSize m)
    return $ Process m
  where
    n = fromIntegral $ natVal (Proxy :: Proxy n)

-- | Helper for deserialization parser monads which will fail when the
-- messages's VC size does not match the type.
guardMessage
    :: forall f n r. (Monad f, Alternative f, KnownNat n)
    => f (Message n r) -> f (Message n r)
guardMessage f = do
    Message m <- f
    guard (n == C.messageSize m)
    return $ Message m
  where
    n = fromIntegral $ natVal (Proxy :: Proxy n)