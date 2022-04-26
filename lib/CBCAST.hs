{-# LANGUAGE StandaloneDeriving #-} -- Show instances of internal CBCAST types
{-# LANGUAGE DeriveGeneric #-} -- Generic instances of internal CBCAST types

-- | External CBCAST client functions which do not require Liquid Haskell for
-- correctness.
module CBCAST
( -- * Initialization
  newProcess
  -- * State transitions
, receive
, deliver
, broadcast
  -- * Types
, CB.PID
, CB.Process
, CB.Message
, content
) where

import GHC.Generics (Generic)
import Text.Printf (printf)
import Control.Arrow (first)

import qualified Redefined
import qualified CBCAST.Transitions
import qualified CBCAST.Core as CB
import qualified CBCAST.Step as CB

-- $setup
-- >>> import Control.Concurrent.STM
-- >>> import CBCAST.Core (Process, mRaw)
-- >>> let m1       = CB.Message [0,1,0]   1 "hello!"
-- >>> let m2       = CB.Message [0,2,0]   1 "world!"
-- >>> let mLongVC  = CB.Message [0,1,0,0] 1 "hello!"
-- >>> let mSamePID = CB.Message [0,0,1]   2 "hello!"
-- >>> sendToCluster _ = return ()

isNat :: Int -> Bool
isNat n = 0 <= n
{-@ inline isNat @-}

isFin :: Redefined.Fin -> Int -> Bool
isFin x n = x < n
{-@ inline isFin @-}

expectedNat :: String -> String
expectedNat = printf "`%s` must be a `Nat`"

expectedFin :: String -> Int -> String
expectedFin = printf "`%s` must be a `Fin %d`"

deriving instance Show r => Show (CB.Process r)
deriving instance Show r => Show (CB.Message r)
deriving instance Show r => Show (CB.Event r)

deriving instance Generic r => Generic (CB.Process r)
deriving instance Generic r => Generic (CB.Message r)
deriving instance Generic r => Generic (CB.Event r)

-- | Extract the content of a message.
-- 
-- >>> content m1
-- "hello!"
-- >>> content m2
-- "world!"
--
content :: CB.Message r -> r
content = CB.mRaw
{-# INLINE content #-}

-- | @newProcess n pid :: Process r@ creates a new CBCAST process with
-- identifier @pid@, for a cluster with @n@ participants, exchanging messages
-- of type @r@.
--
-- >>> newProcess 3 2
-- Right (Process {pVC = [0,0,0], pID = 2, pDQ = [], pHist = []})
--
-- Both @n@ and @pid@ must be /Nat/s. Additionally @pid@ must be a /Fin @n@/.
--
-- >>> newProcess (-3) 2
-- Left "<newProcess n:-3 pid:2>: `n` must be a `Nat`"
-- >>> newProcess 3 (-2)
-- Left "<newProcess n:3 pid:-2>: `pid` must be a `Nat`"
-- >>> newProcess 3 8
-- Left "<newProcess n:3 pid:8>: `pid` must be a `Fin 3`"
--
newProcess :: Int -> CB.PID -> Either String (CB.Process r)
newProcess n pid
    | not $ isNat n     = Left $ prefix ++ expectedNat "n"
    | not $ isNat pid   = Left $ prefix ++ expectedNat "pid"
    | not $ isFin pid n = Left $ prefix ++ expectedFin "pid" n
    | otherwise         = Right $ CB.pEmpty n pid
  where
    prefix = printf "<newProcess n:%d pid:%d>: " n pid

-- | Receive state transition. Call this for messages that arrive from the
-- network, to insert them in the delay queue for later delivery.
--
-- >>> let Right p = newProcess 3 2
-- >>> receive m1 p
-- Right (Process {pVC = [0,0,0], pID = 2, pDQ = [Message {mVC = [0,1,0], mSender = 1, mRaw = "hello!"}], pHist = []})
--
-- The vector clock size of the message must match the vector clock size of the
-- process.
--
-- >>> receive mLongVC p
-- Left "<receive m p>: `messageSize m:4` must equal `processSize p:3`"
--
-- Messages with the sender ID of the current process are ignored (see
-- 'broadcast' to learn how to handle messages from the current process).
--
-- >>> receive mSamePID p
-- Left "<receive m p>: `mSender m:2` must be distinct from `pID p:2`"
--
receive :: CB.Message r -> CB.Process r -> Either String (CB.Process r)
receive m p
    | not $ CB.messageSize m == CB.processSize p    = Left $ printf "<receive m p>: `messageSize m:%d` must equal `processSize p:%d`" (CB.messageSize m) (CB.processSize p)
    | CB.mSender m == CB.pID p                      = Left $ printf "<receive m p>: `mSender m:%d` must be distinct from `pID p:%d`" (CB.mSender m) (CB.pID p)
    | otherwise                                     = let CB.ResultReceive _n ret = CB.step (CB.OpReceive n m) p in Right ret
  where
    n = CB.messageSize m

-- | Deliver state-transition. Call this to check for and return a deliverable
-- message from the delay queue (updating the internal vector clock and history
-- as appropriate).
--
-- >>> let Right p = receive m1 =<< newProcess 3 2
-- >>> deliver p
-- (Just (Message {mVC = [0,1,0], mSender = 1, mRaw = "hello!"}),Process {pVC = [0,1,0], pID = 2, pDQ = [], pHist = [...]})
--
-- When a message is returned, it should be immediately processed by the user
-- application. This should be followed by repeated delivery attempts until
-- nothing is deliverable.
--
-- >>> let Right p = receive m1 =<< newProcess 3 2
-- >>> procVar <- newTVarIO p
-- >>> appVar <- newTVarIO ([] :: [String]) -- Processed commands
-- >>> :{
--     atomically $ do
--         message <- stateTVar procVar deliver
--         maybe retry (\m -> modifyTVar appVar (content m :)) message
--     :}
--
-- >>> readTVarIO appVar
-- ["hello!"]
--
-- When no message in the delay queue is deliverable, @deliver p@ will return
-- @p@ unchanged.
--
-- >>> let Right p = receive m2 =<< newProcess 3 2
-- >>> deliver p
-- (Nothing,Process {pVC = [0,0,0], pID = 2, pDQ = [Message {mVC = [0,2,0], mSender = 1, mRaw = "world!"}], pHist = []})
--
deliver :: CB.Process r -> (Maybe (CB.Message r), CB.Process r)
deliver p = maybe (Nothing, p) (first Just) ret
  where
    n = CB.processSize p `const` ("Proof that processSize returns a Nat", Redefined.listLength $ CB.pVC p)
    CB.ResultDeliver _n ret = CB.step (CB.OpDeliver n) p

-- | Broadcast state transition. Call this to prepare a message for broadcast.
--
-- >>> let Right p = newProcess 3 2
-- >>> broadcast "hooray!" p
-- (Message {mVC = [0,0,1], mSender = 2, mRaw = "hooray!"},Process {pVC = [0,0,1], pID = 2, pDQ = [], pHist = [...]})
--
-- The returned message must be immediately processed by the user application,
-- and then sent on the network to all members of the cluster.
--
-- >>> let Right p = newProcess 3 2
-- >>> procVar <- newTVarIO (p :: Process String)
-- >>> appVar <- newTVarIO ([] :: [String]) -- Processed commands
-- >>> :{
--     do m <- atomically $ do
--            message <- stateTVar procVar $ broadcast "hooray!"
--            modifyTVar appVar (content message :)
--            return message
--        sendToCluster m
--     :}
--
-- >>> readTVarIO appVar
-- ["hooray!"]
--
broadcast :: r -> CB.Process r -> (CB.Message r, CB.Process r)
broadcast raw p = ret
  where
    n = CB.processSize p `const` ("Proof that processSize returns a Nat", Redefined.listLength $ CB.pVC p)
    CB.ResultBroadcast _n ret = CB.step (CB.OpBroadcast n raw) p
