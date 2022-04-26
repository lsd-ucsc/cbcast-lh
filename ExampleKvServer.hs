{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC "-Wno-orphans" #-}

module Main where

import Control.Monad.IO.Class (liftIO)
import Data.Monoid (Sum(..))
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
import qualified Network.Wai.Middleware.Gzip as Gzip
import qualified System.Environment as Env
import qualified System.IO as IO

import qualified Network.Wai.Metrics as Metrics
import qualified System.Remote.Monitoring as EKG
import qualified System.Metrics as EKG
import qualified System.Metrics.Counter as Counter
import qualified System.Metrics.Distribution as Distribution

import Servant
import Servant.API.Generic ((:-), Generic, ToServantApi)
import qualified Servant.Client as Servant
import qualified Servant.Client.Generic as Servant

import qualified CBCAST
import qualified CBCAST.Core

-- $setup
-- >>> :{
--  testCoalesce pred monoids = do
--      q <- STM.newTQueueIO
--      print =<< (STM.atomically $ do
--          mapM_ (STM.writeTQueue q) monoids
--          coalesceWhile pred q)
--      print =<< (STM.atomically $ STM.flushTQueue q)
-- :}




-- * KV Application

type Key = String
type Val = Aeson.Value

data KvCommand
    = KvPut Key Val
    | KvDel Key
    deriving (Generic, Show, Eq)

-- | State of the KV Store
type KvState = Map.Map Key Val

-- | Interpret a command to update KV Store state
kvApply :: KvCommand -> KvState -> KvState
kvApply (KvPut key val) = Map.insert key val
kvApply (KvDel key) = Map.delete key

kvQuery :: Key -> KvState -> Maybe Val
kvQuery key = Map.lookup key

-- | Client routes exposed by the KV Store
data KvRoutes mode = KvRoutes
    { kvPut :: mode :- "kv" :> Capture "key" Key :> ReqBody '[JSON] Val :> PutNoContent
    , kvDel :: mode :- "kv" :> Capture "key" Key :> DeleteNoContent
    , kvGet :: mode :- "kv" :> Capture "key" Key :> Get '[JSON] Val
    }
    deriving (Generic)

-- | Apply a message to application state.
applyMessage :: STM.TVar KvState -> Broadcast -> STM.STM ()
applyMessage kvState m =
    STM.modifyTVar' kvState . kvApply $ CBCAST.content m




-- * CBCAST Node & Peers

-- | State of the CBCAST node
type NodeState = CBCAST.Process KvCommand

-- | Type of messages exchanged by CBCAST nodes
type Broadcast = CBCAST.Message KvCommand

-- | Routes exposed by the CBCAST node 
data PeerRoutes mode = PeerRoutes
    -- We coalesce CBCASTs by sending a list of them in each request.
    { cbcast :: mode :- "cbcast" :> ReqBody '[JSON] [Broadcast] :> PostNoContent
    }
    deriving (Generic)

peerRoutes :: PeerRoutes (Servant.AsClientT Servant.ClientM)
peerRoutes = Servant.genericClient

-- | Type of coalesced broadcasts stored in outbound buffers for other CBCAST
-- nodes. The count is the number of failed requests to the recipient.
type Coalesced = (Sum Int, [Broadcast])

-- | Addresses of other CBCAST nodes
type Peers = [Servant.BaseUrl]

-- | Outbound buffers for other CBCAST nodes
type PeerQueues = [STM.TQueue Coalesced]

-- | Put a message on all peer queues.
feedPeerQueues :: PeerQueues -> Broadcast -> STM.STM ()
feedPeerQueues peerQueues m =
    Monad.forM_ peerQueues $ \q ->
        STM.writeTQueue q (0, [m])




-- * Serialization Instances

instance Aeson.ToJSON   KvCommand
instance Aeson.FromJSON KvCommand

-- | Serialization round-tripper!
--
-- >>> let Right p = CBCAST.newProcess 3 0
-- >>> let (m, p') = CBCAST.broadcast (KvPut "some-key" Aeson.Null) p
-- >>> let m' = Aeson.decode $ Aeson.encode m :: Maybe Broadcast
-- >>> Just m == m'
-- True
--
-- >>> import Data.ByteString.Lazy.Char8 as BS
-- >>> BS.putStrLn $ Aeson.encode m'
-- {"mVC":[1,0,0],"mSender":0,"mRaw":{"tag":"KvPut","contents":["some-key",null]}}
--
instance (Generic r, Aeson.ToJSON   r) => Aeson.ToJSON   (CBCAST.Message r)
instance (Generic r, Aeson.FromJSON r) => Aeson.FromJSON (CBCAST.Message r)




-- * Backend

-- ** Request handlers

-- | Monitoring counters
data Stats = Stats
    { deliverCount :: Counter.Counter
    , receiveCount :: Counter.Counter
    , receivedIsDeliverable :: Distribution.Distribution
    , broadcastCount :: Counter.Counter
    , unicastAttemptSuccessful :: Distribution.Distribution
    , unicastSuccessSize :: Distribution.Distribution
    }

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
             STM.atomically $ do
                m <- STM.stateTVar nodeState . CBCAST.broadcast $ KvPut key val
                applyMessage kvState m -- apply message locally
                feedPeerQueues peerQueues m -- nonblocking send message to network
             Counter.inc $ broadcastCount stats
             return NoContent)
        :<|> (\key -> liftIO $ do
             STM.atomically $ do
                m <- STM.stateTVar nodeState . CBCAST.broadcast $ KvDel key
                applyMessage kvState m -- apply message locally
                feedPeerQueues peerQueues m -- nonblocking send message to network
             Counter.inc $ broadcastCount stats
             return NoContent)
        :<|> (\key -> do
                kv <- liftIO $ STM.readTVarIO kvState
                maybe (throwError err404) return $ kvQuery key kv)
    nodeHandlers :: Server (ToServantApi PeerRoutes)
    nodeHandlers
        =    (\messages -> liftIO $ do
             mapM_ receiveOne messages
             return NoContent)
    receiveOne m = do
        status <- STM.atomically $ do
            -- observe deliverability; receive message into delay queue
            deliverable <- STM.readTVar nodeState >>= \p ->
                return $ CBCAST.Core.deliverable m (CBCAST.Core.pVC p)
            receiveErr <- STM.stateTVar nodeState $ \p ->
                either ((,p) . Just) (Nothing,) $ CBCAST.receive m p
            return $ maybe (Right deliverable) Left receiveErr
        case status of
            Left e -> printf "receive error: %s\n" e
            Right deliverable -> do
                -- Count received messages and compute p(deliverable|received)
                Counter.inc (receiveCount stats)
                Distribution.add (receivedIsDeliverable stats) (if deliverable then 1 else 0)



-- ** Deliver messages

-- | Block until there is a deliverable message and apply it. Best used with
-- 'Monad.forever'.
readMailOnce :: STM.TVar NodeState -> STM.TVar KvState -> STM.STM ()
readMailOnce nodeState kvState = do
    message <- STM.stateTVar nodeState CBCAST.deliver
    maybe STM.retry (applyMessage kvState) message

-- ** Broadcast messages

-- | Drain broadcast messages and send them to peers, forever. Does not return.
sendMailThread :: Stats -> Peers -> PeerQueues -> IO ()
sendMailThread stats peers peerQueues =
  Exc.assert (length peers == length peerQueues) $ do
    printf "sendMailThread will deliver to peers: %s\n" (unwords $ Servant.showBaseUrl <$> peers)
    connections <- HTTP.newManager HTTP.defaultManagerSettings
    let clientEnvs = Servant.mkClientEnv connections <$> peers
    -- Start tasks and wait forever.
    -- Note: Graceful shutdown is not implemented.
    (_, result)
        <- Async.waitAnyCatchCancel
        =<< mapM (Async.async . Monad.void . Monad.forever)
        (sendToPeer stats <$> zip clientEnvs peerQueues)
    printf "sendMailThread exited: %s\n" $ show result

-- | Send a message from a queue to a peer. On failure, backoff and put the
-- message back on the queue and note failure. Return.
sendToPeer :: Stats -> (Servant.ClientEnv, STM.TQueue Coalesced) -> IO ()
sendToPeer stats (env, queue) = do
    (Sum failures, message) <- STM.atomically $ do
        coalesced <- coalesceWhile (\(_, xs) -> length xs < 10) queue
        STM.check $ mempty /= coalesced
        return coalesced
    result <- Servant.runClientM (cbcast peerRoutes message) env
    case result of
        Right NoContent -> do
            Distribution.add (unicastAttemptSuccessful stats) 1
            Distribution.add (unicastSuccessSize stats) (fromIntegral $ length message)
        Left err -> do
            Distribution.add (unicastAttemptSuccessful stats) 0
            printf "sendToPeer error (%d, %s): %s \n" failures (Servant.showBaseUrl $ Servant.baseUrl env) (showClientError err)
            backoff <- STM.registerDelay $ round (2^(min 5 failures) * 1e6 :: Double)
            STM.atomically $ do
                STM.check =<< STM.readTVar backoff
                STM.unGetTQueue queue (Sum $ failures + 1, message)

-- | Coalesce monoids from a queue while a predicate is satisfied.
--
-- Stop when the predicate is no longer satisfied by the coalesced monoid.
--
-- >>> testCoalesce (< 5) $ fmap Sum [1,3,5,2,4]
-- Sum {getSum = 9}
-- [Sum {getSum = 2},Sum {getSum = 4}]
--
-- Always make a little progress.
--
-- >>> testCoalesce (< 5) $ fmap Sum [99,3,5,2,4]
-- Sum {getSum = 99}
-- [Sum {getSum = 3},Sum {getSum = 5},Sum {getSum = 2},Sum {getSum = 4}]
--
-- Coalesce in FIFO-order.
--
-- >>> testCoalesce (\x -> length x < 10) $ words "too many ducks and not enough pond"
-- "toomanyducks"
-- ["and","not","enough","pond"]
--
-- Stop when the queue is exausted.
--
-- >>> testCoalesce (const True) $ fmap Sum [1,3,5,2,4]
-- Sum {getSum = 15}
-- []
--
-- Return @mempty@ when the queue is empty.
--
-- >>> testCoalesce (const True) $ fmap Sum []
-- Sum {getSum = 0}
-- []
--
coalesceWhile :: Monoid a => (a -> Bool) -> STM.TQueue a -> STM.STM a
coalesceWhile more queue = f mempty
  where
    f x | more x    = maybe (return x) (f . (x <>)) =<< STM.tryReadTQueue queue
        | otherwise = return x




-- * Demo

-- | Try starting the server and hitting it with these commands:
--
-- $ curl 127.0.0.1:8080/kv/foo
-- $ curl -X DELETE 127.0.0.1:8080/kv/foo
-- $ curl -X PUT -H "Content-type: application/json" 127.0.0.1:8080/kv/foo -d '{"x":1,"y":20}'
--
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
        -- !!! Set up monitoring
        metricsStore <- mkMetricsStore
        stats <- processMetrics metricsStore
        metricsMiddleware <- waiMetricsMiddleware metricsStore
        -- !!! Set up cluster
        peers <- mapM Servant.parseBaseUrl urls
        pid <- either fail return $ parsePID num peers
        let port = Servant.baseUrlPort $ peers !! pid
        printf "Starting KV server PID-%d on port %d with peer list: %s\n" pid port (unwords $ Servant.showBaseUrl <$> peers)
        nodeState <- either fail STM.newTVarIO $ CBCAST.newProcess (length peers) pid
        kvState <- STM.newTVarIO $ Map.empty
        -- Note: One fewer peer queue because we don't send to ourselves.
        peerQueues <- sequence $ replicate (length peers - 1) STM.newTQueueIO
        -- Start tasks and wait forever.
        -- Note: Graceful shutdown is not implemented.
        (_, result)
            <- Async.waitAnyCatchCancel
            =<< mapM Async.async
            [ Monad.forever $ do
                STM.atomically $ readMailOnce nodeState kvState
                Counter.inc (deliverCount stats)
            -- Note: sendMailThread does not receive the url of the current process.
            , sendMailThread stats (removeIndex pid peers) peerQueues
            -- Note: Server listens on the port specified in the peer list.
            , Warp.run port
                . metricsMiddleware
                . Gzip.gzip Gzip.def
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
        <*> EKG.createCounter "cbcast.receiveCount" store
        <*> EKG.createDistribution "cbcast.receivedIsDeliverable" store
        <*> EKG.createCounter "cbcast.broadcastCount" store
        <*> EKG.createDistribution "cbcast.unicastAttemptSuccessful" store
        <*> EKG.createDistribution "cbcast.unicastSuccessSize" store




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
parsePID :: String -> [a] -> Either String CBCAST.PID
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
