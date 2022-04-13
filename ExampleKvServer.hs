{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# OPTIONS_GHC "-Wno-orphans" #-}
module Main where

import Control.Monad.IO.Class (liftIO)
import Text.Printf (printf)
import Text.Read (readEither)
import qualified Control.Exception as Exc
import qualified Control.Concurrent.Async as Async
import qualified Control.Concurrent.STM as STM
import qualified Control.Monad as Monad
import qualified Data.Aeson as Aeson
import qualified Data.Map as Map
import qualified Network.HTTP.Client as HTTP
import qualified Network.Wai.Handler.Warp as Warp
import qualified System.Environment as Env
import qualified System.IO as IO

import qualified Network.Wai.Metrics as Metrics
import qualified System.Remote.Monitoring as EKG
import qualified System.Metrics as EKG
import qualified System.Metrics.Counter as Counter
import System.IO.Unsafe (unsafePerformIO) -- To collect stats within an STM transaction

import Servant
import Servant.API.Generic ((:-), Generic, ToServantApi)
import qualified Servant.Client as Servant
import qualified Servant.Client.Generic as Servant

import qualified MessagePassingAlgorithm as MPA
import qualified MessagePassingAlgorithm.VectorClockAdapter as VCA
import qualified MessagePassingAlgorithm.CBCAST as CBCAST

-- * KV Application

type Key = String
type Val = Aeson.Value

data KvCommand
    = KvPut Key Val
    | KvDel Key
    deriving (Generic, Show, Eq)

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


-- * CBCAST Node & Peers

type Broadcast = VCA.M KvCommand

type NodeState = CBCAST.P KvCommand

data PeerRoutes mode = PeerRoutes
    { cbcast :: mode :- "cbcast" :> ReqBody '[JSON] Broadcast :> PostNoContent
    }
    deriving (Generic)

type Peers = [Servant.BaseUrl]

peerRoutes :: PeerRoutes (Servant.AsClientT Servant.ClientM)
peerRoutes = Servant.genericClient

type PeerQueues = [STM.TQueue (Int, Broadcast)]


-- * Backend


-- ** Handle requests

-- | Handle requests to send or receive messages.
handlers :: Stats -> PeerQueues -> STM.TVar NodeState -> STM.TVar KvState -> Application
handlers stats peerQueues nodeState kvState = serve
    (Proxy :: Proxy (ToServantApi KvRoutes :<|> ToServantApi PeerRoutes))
    (kvHandlers :<|> nodeHandlers)
  where
    -- https://github.com/haskell-servant/servant/issues/1394
    kvHandlers :: Server (ToServantApi KvRoutes)
    kvHandlers
        =    (\key val -> liftIO $ do
             Counter.inc (broadcastCount stats)
             STM.atomically $ do
                m <- STM.stateTVar nodeState . CBCAST.internalBroadcast $ KvPut key val
                feedPeerQueues peerQueues m -- send message to network
                applyMessage kvState m -- apply message locally
                return NoContent)
        :<|> (\key -> liftIO $ do
             Counter.inc (broadcastCount stats)
             STM.atomically $ do
                m <- STM.stateTVar nodeState . CBCAST.internalBroadcast $ KvDel key
                feedPeerQueues peerQueues m -- send message to network
                applyMessage kvState m -- apply message locally
                return NoContent)
        :<|> (\key -> do
                kv <- liftIO $ STM.readTVarIO kvState
                maybe (throwError err404) return $ kvQuery key kv)
    nodeHandlers :: Server (ToServantApi PeerRoutes)
    nodeHandlers
        =    (\message -> liftIO $ do
             Counter.inc (receiveCount stats)
             STM.atomically $ do
                STM.modifyTVar' nodeState $ CBCAST.internalReceive message
                return NoContent)


-- ** Deliver messages

-- | Block until there is a deliverable message and apply it.
--
-- TODO tests
readMail :: Stats -> STM.TVar NodeState -> STM.TVar KvState -> STM.STM ()
readMail stats nodeState kvState = do
    p₀ <- STM.readTVar nodeState
    case CBCAST.internalDeliver p₀ of
        Nothing -> do
            return . unsafePerformIO . Counter.inc $ deliverFailCount stats
            STM.retry
        Just (m, p₁) -> do
            return . unsafePerformIO . Counter.inc $ deliverCount stats
            applyMessage kvState m
            STM.writeTVar nodeState p₁

-- | Apply the message to application state.
applyMessage :: STM.TVar KvState -> Broadcast -> STM.STM ()
applyMessage kvState m =
    STM.modifyTVar' kvState . kvApply . MPA.mRaw $ m


-- ** Broadcast messages

-- | Drain broadcast messages and send them to peers, forever. Does not return.
sendMailThread :: Peers -> PeerQueues -> IO ()
sendMailThread peers peerQueues = Exc.assert (length peers == length peerQueues) $ do
    printf "sendMailThread will deliver to peers: %s\n" (unwords $ Servant.showBaseUrl <$> peers)
    connections <- HTTP.newManager HTTP.defaultManagerSettings
    let clientEnvs = Servant.mkClientEnv connections <$> peers
    -- Start tasks and wait forever.
    -- Note: Graceful shutdown is not implemented.
    (_, result)
        <- Async.waitAnyCatchCancel
        =<< mapM (Async.async . Monad.void . Monad.forever)
        (sendToPeer <$> zip clientEnvs peerQueues)
    printf "sendMailThread exited: %s\n" $ show result

-- | Put the message on all peer queues.
--
-- TODO tests
feedPeerQueues :: PeerQueues -> Broadcast -> STM.STM ()
feedPeerQueues peerQueues m =
    Monad.forM_ peerQueues $ \q ->
        STM.writeTQueue q (0, m)

-- | Send a message from a queue to a peer. On failure, backoff and put the
-- message back on the queue and note failure. Return.
--
-- TODO tests
sendToPeer :: (Servant.ClientEnv, STM.TQueue (Int, Broadcast)) -> IO ()
sendToPeer (env, queue) = do
    (failures, message) <- STM.atomically $ STM.readTQueue queue
    result <- Servant.runClientM (cbcast peerRoutes message) env
    case result of
        Right NoContent -> return ()
        Left err -> do
            printf "sendToPeer error (%d, %s): %s \n" failures (Servant.showBaseUrl $ Servant.baseUrl env) (showClientError err)
            backoff <- STM.registerDelay $ round (2^failures * 1e6 :: Double)
            STM.atomically $ do
                STM.check =<< STM.readTVar backoff
                STM.unGetTQueue queue (min 9 $ failures + 1, message)


-- * Demo

-- | Try starting the server and hitting it with these commands:
--
-- $ curl 127.0.0.1:8080/kv/foo
-- $ curl -X DELETE 127.0.0.1:8080/kv/foo
-- $ curl -X PUT -H "Content-type: application/json" 127.0.0.1:8080/kv/foo -d '{"x":1,"y":20}'
main :: IO ()
main = Env.getArgs >>= \argv -> case argv of
    [] -> do
        prog <- Env.getProgName
        putStrLn "USAGE:"
        putStrLn $ "\t" ++ prog ++ " URL -- KV Client"
        putStrLn "\t\tGenerate a sequence of random KV store requests and send them to the specified URL."
        putStrLn ""
        putStrLn $ "\t" ++ prog ++ " NUM URL [URL ...] -- KV Server & CBCAST Node"
        putStrLn $ "\t\t" ++ unwords
            [ "Start a KV server."
            , "At least one URL must be provided."
            , "The URLs are regarded as peers in the CBCAST cluster."
            , "The NUM is an offset into the list of peers to indicate which corresponds to this host."
            , "All peers must be provided with the same list of peers (order matters), and distinct NUMs."
            ]
    [url] -> do
        server <- Servant.parseBaseUrl url
        printf "Starting KV client sticky to server: %s\n" $ Servant.showBaseUrl server
        putStrLn "not implemented"
    (num:urls) -> do
        -- Note: Ensure buffering is set so that stdout goes to syslog.
        IO.hSetBuffering IO.stdout IO.LineBuffering
        metricsStore <- mkMetricsStore
        stats <- processMetrics metricsStore
        metricsMiddleware <- waiMetricsMiddleware metricsStore
        peers <- mapM Servant.parseBaseUrl urls
        pid <- either fail return $ parsePID num peers
        let port = Servant.baseUrlPort $ peers !! pid
        printf "Starting KV server P%d on port %d with peer list: %s\n" pid port (unwords $ Servant.showBaseUrl <$> peers)
        nodeState <- STM.newTVarIO $ CBCAST.pEmpty (length peers) pid
        kvState <- STM.newTVarIO $ Map.empty
        -- Note: One fewer peer queue because we don't send to ourselves.
        peerQueues <- sequence $ replicate (length peers - 1) STM.newTQueueIO
        -- Start tasks and wait forever.
        -- Note: Graceful shutdown is not implemented.
        (_, result)
            <- Async.waitAnyCatchCancel
            =<< mapM Async.async
            [ Monad.forever . STM.atomically $ readMail stats nodeState kvState
            -- Note: sendMailThread does not receive the url of the current process.
            , sendMailThread (removeIndex pid peers) peerQueues
            -- Note: Server listens on the port specified in the peer list.
            , Warp.run port
                . metricsMiddleware
                $ handlers stats peerQueues nodeState kvState
            ]
        printf "main thread exited: %s\n" $ show result
        return ()
  where
    mkMetricsStore = do
        let metricsHost = "localhost"
            metricsPort = 9890
        printf "Starting metrics server on %s and %d\n" (show metricsHost) metricsPort
        server <- EKG.forkServer metricsHost metricsPort
        return $ EKG.serverMetricStore server
    waiMetricsMiddleware store = do
        metrics <- Metrics.registerWaiMetrics store
        return $ Metrics.metrics metrics
    processMetrics store = Stats
        <$> EKG.createCounter "cbcast.deliverCount" store
        <*> EKG.createCounter "cbcast.deliverFailCount" store
        <*> EKG.createCounter "cbcast.receiveCount" store
        <*> EKG.createCounter "cbcast.broadcastCount" store

data Stats = Stats
    { deliverCount :: Counter.Counter
    , deliverFailCount :: Counter.Counter
    , receiveCount :: Counter.Counter
    , broadcastCount :: Counter.Counter
    }


-- * Serialization Instances

instance Aeson.ToJSON KvCommand
instance Aeson.FromJSON KvCommand

deriving instance Generic VCA.VCMM
instance Aeson.ToJSON VCA.VCMM
instance Aeson.FromJSON VCA.VCMM

-- |
--
-- >>> let mm = VCA.VCMM [1, 4] 1
-- >>> let m = MPA.Message mm (KvPut "some-key" Aeson.Null) :: Broadcast
-- >>> let m' = Aeson.decode $ Aeson.encode m :: Maybe Broadcast
-- >>> Just m == m'
-- True
--
-- >>> import Data.ByteString.Lazy.Char8 as BS
-- >>> BS.putStrLn $ Aeson.encode m'
-- {"mMetadata":{"vcmmSender":1,"vcmmSent":[1,4]},"mRaw":{"tag":"KvPut","contents":["some-key",null]}}
--
deriving instance (Generic mm, Generic r) => Generic (MPA.Message mm r)
instance (Generic mm, Generic r, Aeson.ToJSON mm, Aeson.ToJSON r) => Aeson.ToJSON (MPA.Message mm r)
instance (Generic mm, Generic r, Aeson.FromJSON mm, Aeson.FromJSON r) => Aeson.FromJSON (MPA.Message mm r)


-- * Helpers

-- | Parse a CBCAST PID with useful error messages.
--
-- >>> parsePID "2" [undefined, undefined, undefined]
-- Right 2
--
-- >>> parsePID "4" [undefined, undefined, undefined]
-- Left "invalid integer range 4, should be (0,3]"
-- >>> parsePID "foo" [undefined, undefined, undefined]
-- Left "invalid integer literal 'foo'"
parsePID :: String -> [a] -> Either String MPA.PID
parsePID s xs = case readEither s of
    Left _ -> Left $ printf "invalid integer literal '%s'" s
    Right n
        | 0 <= n && n < length xs -> Right n
        | otherwise -> Left $ printf "invalid integer range %d, should be (0,%d]" n (length xs)

-- | Remove the specified index from the list.
--
-- >>> removeIndex 0 "abc"
-- "bc"
-- >>> removeIndex 2 "abc"
-- "ab"
--
-- >>> removeIndex (-1) "abc"
-- "abc"
-- >>> removeIndex 10 "abc"
-- "abc"
--
removeIndex :: Int -> [a] -> [a]
removeIndex n xs
    | 0 <= n && n < length xs = let (before, after) = splitAt n xs in before ++ tail after
    | otherwise = xs

-- | Render client errors for better log messages.
showClientError :: Servant.ClientError -> String
showClientError err = case err of
    Servant.FailureResponse _RequestF response          -> summarize "FailureResponse" response
    Servant.DecodeFailure _Text response                -> summarize "DecodeFailure" response
    Servant.UnsupportedContentType mediaType response   -> summarize (printf "UnsupportedContentType: %s" $ show mediaType) response
    Servant.InvalidContentTypeHeader response           -> summarize "InvalidContentTypeHeader" response
    Servant.ConnectionError someException -> printf "ConnectionError: %s" $ show someException
  where
    summarize :: String -> Servant.Response -> String
    summarize cat resp = printf "%s: %s" cat (show $ Servant.responseStatusCode resp)
