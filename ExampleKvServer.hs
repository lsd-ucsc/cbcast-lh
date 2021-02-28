{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# OPTIONS_GHC "-Wno-orphans" #-}
module Main where

import Control.Monad.IO.Class (liftIO)
import Data.Foldable (foldl')
import Data.Tuple (swap)
import qualified Control.Concurrent.Async as Async
import qualified Control.Concurrent.STM as STM
import qualified Control.Monad as Monad
import qualified Data.Aeson as Aeson
import qualified Data.Map as Map
import qualified Network.HTTP.Client as HTTP
import qualified Network.Wai.Handler.Warp as Warp

import Servant
import Servant.API.Generic ((:-), Generic, ToServantApi, genericApi)
import Servant.Client as Servant
import Servant.Client.Generic as Servant

import qualified Causal.CBCAST.VectorClock as CBCAST
import qualified Causal.CBCAST.Message as CBCAST
import qualified Causal.CBCAST.Process as CBCAST
import qualified Causal.CBCAST.Protocol as CBCAST


-- * KV Application

type Key = String
type Val = Aeson.Value

data KvCommand
    = KvPut Key Val
    | KvDel Key
    deriving (Generic, Show)

type KvState = Map.Map Key Val

kvApply :: KvCommand -> KvState -> KvState
kvApply (KvPut key val) = Map.insert key val
kvApply (KvDel key) = Map.delete key

kvQuery :: Key -> KvState -> Maybe Val
kvQuery key = Map.lookup key

data KvRoutes mode = KvRoutes
    { kvPut :: mode :- "kv" :> Capture "key" Key :> ReqBody '[JSON] Val :> PutNoContent
    , kvDel :: mode :- "kv" :> Capture "key" Key :> DeleteNoContent
    , kvGet :: mode :- "kv" :> Capture "key" Key :> Get '[JSON] Val
    }
    deriving (Generic)


-- * CBCAST Peer

type Broadcast = CBCAST.Message KvCommand

type PeerState = CBCAST.Process KvCommand

data PeerRoutes mode = PeerRoutes
    { cbcast :: mode :- "receive-cbcast" :> ReqBody '[JSON] Broadcast :> PostNoContent
    }
    deriving (Generic)

type Peers = [Servant.BaseUrl]


-- * Backend

handlers :: STM.TVar PeerState -> STM.TVar KvState -> Application
handlers peerState kvState = serve
    (Proxy :: Proxy (ToServantApi KvRoutes :<|> ToServantApi PeerRoutes))
    (kvHandlers :<|> peerHandlers)
  where
    -- https://github.com/haskell-servant/servant/issues/1394
    kvHandlers :: Server (ToServantApi KvRoutes)
    kvHandlers
        =    (\key val -> liftIO . STM.atomically $ do
                STM.modifyTVar' peerState . CBCAST.send $ KvPut key val
                readMail peerState kvState
                return NoContent)
        :<|> (\key -> liftIO . STM.atomically $ do
                STM.modifyTVar' peerState . CBCAST.send $ KvDel key
                readMail peerState kvState
                return NoContent)
        :<|> (\key -> do
                kv <- liftIO $ STM.readTVarIO kvState
                maybe (throwError err404) return $ kvQuery key kv)
    peerHandlers :: Server (ToServantApi PeerRoutes)
    peerHandlers
        =    (\message -> liftIO . STM.atomically $ do
                STM.modifyTVar' peerState $ CBCAST.receive message
                readMail peerState kvState
                return NoContent)

-- | Drain delivered messages and apply them to application state.
readMail :: STM.TVar PeerState -> STM.TVar KvState -> STM.STM ()
readMail peerState kvState = do
    deliveries <- STM.stateTVar peerState $ swap . CBCAST.drainDeliveries
    STM.modifyTVar' kvState $ \kv -> foldl' (flip kvApply) kv $ fmap CBCAST.mRaw deliveries

-- | 
sendMailThread :: Peers -> STM.TVar PeerState -> IO ()
sendMailThread peers peerState = do
    manager <- HTTP.newManager HTTP.defaultManagerSettings
    peerQueues <- sequence $ replicate (length peers) STM.newTQueueIO
    peerThreads <- Monad.forM_ (zip peerQueues peers) $ \(queue, url) -> Async.async $ do
        let env = Servant.mkClientEnv manager url
        msg <- STM.atomically $ STM.readTQueue queue
        return ()

--  putStrLn . ("sendMailThread exited: " ++) . show . snd
--      =<< Async.waitAnyCatchCancel
--      =<< mapM Async.async []

--  let x = ( Monad.forever . STM.atomically $ do
--              ms <- STM.stateTVar peerState $ swap . CBCAST.drainBroadcasts
--              if null ms then STM.retry else mapM_ (STM.writeTQueue outbox) ms
--          )
--          -- FIXME: wrong approach; we want one thread per destination
--          -- or possibly one buffer per destination
--          : replicate sendConc
--          ( Monad.forever $ do
--              print 10 -- send message to every host
--          )

    return ()

-- * Demo

sendConc :: Int
sendConc = 10

main :: IO ()
main = do
    let m = CBCAST.Message 1 (CBCAST.VC [1, 4]) (KvPut "record" Aeson.Null) :: Broadcast
    print (Aeson.decode . Aeson.encode $ m :: Maybe Broadcast)

    let peers = undefined :: Peers
    let ownPid = undefined :: Int
    peerState <- STM.newTVarIO $ CBCAST.pNew ownPid (length peers)
    kvState <- STM.newTVarIO $ Map.empty
--  withAsync
--      (sendMailThread peers
    Warp.run 8080 $ handlers peerState kvState



-- * Instances

instance Aeson.ToJSON KvCommand
instance Aeson.FromJSON KvCommand

deriving instance Generic CBCAST.VC
instance Aeson.ToJSON CBCAST.VC
instance Aeson.FromJSON CBCAST.VC

deriving instance Show r => Show (CBCAST.Message r)
deriving instance Generic r => Generic (CBCAST.Message r)
instance (Generic r, Aeson.ToJSON r) => Aeson.ToJSON (CBCAST.Message r)
instance (Generic r, Aeson.FromJSON r) => Aeson.FromJSON (CBCAST.Message r)
