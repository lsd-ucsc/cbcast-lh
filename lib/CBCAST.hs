{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-} -- Must use "forall" to introduce them
{-# LANGUAGE TypeFamilies #-} -- For ~ constraint
{-# LANGUAGE StandaloneDeriving #-} -- Show instances of internal CBCAST types

-- | External CBCAST client functions which do not require Liquid Haskell for
-- correctness.
module CBCAST
where
-- ( Process
-- , Message
-- , guardProcess
-- , guardMessage
-- ) where

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

-- | CBCAST process for a cluster with @n@ participants.
newtype Process (n :: Nat) r = Process (C.Process r)
    deriving Show

-- | CBCAST mssage for a cluster with @n@ participants.
newtype Message (n :: Nat) r = Message (C.Message r)
    deriving Show

-- | Create a new process for a cluster with @n@ participants exchanging
-- messages of type @r@. The process identifier is given in the phantom of
-- @Proxy @pid@.
--
-- >>> :set -XDataKinds
-- >>> :set -XTypeApplications
-- >>> newProcess (Proxy @2) :: Process 3 String
-- Process (Process {pVC = [0,0,0], pID = 2, pDQ = [], pHist = []})
--
-- The process identifier must be a natural less than @n@.
--
-- >>> CBCAST.newProcess (Proxy @8) :: Process 3 String
-- ...
-- ... Couldn't match type ‘'GT’ with ‘'LT’
-- ...
--
{-@ ignore newProcess @-}
newProcess
    :: forall pid n r. (KnownNat pid, KnownNat n, CmpNat pid n ~ 'LT)
    => Proxy pid -> Process n r
newProcess pidProxy = Process $ C.pEmpty n pid
  where
    n = fromIntegral $ natVal (Proxy :: Proxy n)
    pid = fromIntegral $ natVal pidProxy

-- | Create a new process ...
newProcess'
    :: Int -> Int -> Maybe (Process n r)
newProcess' = undefined

-- | Receive state transition. Call this for messages that arrive from the
-- network, to insert them in the delay queue for later delivery. Messages with
-- the sender ID of the current process are ignored.
--
{-@ ignore receive @-}
receive
    :: forall n r. KnownNat n
    => Message n r -> Process n r -> Process n r
receive (Message m) (Process p) = Process ret
  where
    n = fromIntegral $ natVal (Proxy :: Proxy n)
    S.ResultReceive _n ret = S.step (S.OpReceive n m) p

-- | Deliver state-transition. Call this to check for and return a deliverable
-- message from the delay queue (updating the internal vector clock and history
-- as appropriate). When a message is returned, it should immediately be
-- processed by the user application.
--
{-@ ignore deliver @-}
deliver
    :: forall n r. KnownNat n
    => Process n r -> Maybe (Message n r, Process n r)
deliver (Process p) = fmap (bimap Message Process) ret
  where
    n = fromIntegral $ natVal (Proxy :: Proxy n)
    S.ResultDeliver _n ret = S.step (S.OpDeliver n) p

-- | Broadcast state transition. Call this to prepare a message for broadcast.
-- The returned message must be immediately processed by the user application,
-- and then sent on the network to all members of the cluster.
--
{-@ ignore broadcast @-}
broadcast
    :: forall n r. KnownNat n
    => r -> Process n r -> (Message n r, Process n r)
broadcast raw (Process p) = bimap Message Process ret
  where
    n = fromIntegral $ natVal (Proxy :: Proxy n)
    S.ResultBroadcast _n ret = S.step (S.OpBroadcast n raw) p


-- | Deserialization helper. Call this to ensure the process' vector clock size
-- matches its type.
guardProcess
    :: forall f n r. (Monad f, Alternative f, KnownNat n)
    => f (Process n r) -> f (Process n r)
guardProcess f = do
    Process m <- f
    guard (n == C.processSize m)
    return $ Process m
  where
    n = fromIntegral $ natVal (Proxy :: Proxy n)

-- | Deserialization helper. Call this to ensure the message's vector clock
-- size matches its type.
guardMessage
    :: forall f n r. (Monad f, Alternative f, KnownNat n)
    => f (Message n r) -> f (Message n r)
guardMessage f = do
    Message m <- f
    guard (n == C.messageSize m)
    return $ Message m
  where
    n = fromIntegral $ natVal (Proxy :: Proxy n)
