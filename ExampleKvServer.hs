{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# OPTIONS_GHC "-Wno-orphans" #-}
module Main where

import Control.Monad.IO.Class (liftIO)
import Data.Tuple (swap)
import Text.Printf (printf)
import Text.Read (readEither)
import qualified Control.Concurrent.Async as Async
import qualified Control.Concurrent.STM as STM
import qualified Control.Monad as Monad
import qualified Data.Aeson as Aeson
import qualified Data.Map as Map
import qualified Network.HTTP.Client as HTTP
import qualified Network.Wai.Handler.Warp as Warp
import qualified System.Environment as Env

import Servant
import Servant.API.Generic ((:-), Generic, ToServantApi)
import qualified Servant.Client as Servant
import qualified Servant.Client.Generic as Servant

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

type Broadcast = CBCAST.Message KvCommand

type NodeState = CBCAST.Process KvCommand

data PeerRoutes mode = PeerRoutes
    { cbcast :: mode :- "receive-cbcast" :> ReqBody '[JSON] Broadcast :> PostNoContent
    }
    deriving (Generic)

type Peers = [Servant.BaseUrl]

peerRoutes :: PeerRoutes (Servant.AsClientT Servant.ClientM)
peerRoutes = Servant.genericClient


-- * Backend


-- ** Handle requests

-- | Handle requests to send or receive messages.
handlers :: STM.TVar NodeState -> STM.TVar KvState -> Application
handlers nodeState kvState = serve
    (Proxy :: Proxy (ToServantApi KvRoutes :<|> ToServantApi PeerRoutes))
    (kvHandlers :<|> nodeHandlers)
  where
    -- https://github.com/haskell-servant/servant/issues/1394
    kvHandlers :: Server (ToServantApi KvRoutes)
    kvHandlers
        =    (\key val -> liftIO . STM.atomically $ do
                STM.modifyTVar' nodeState . CBCAST.send $ KvPut key val
                return NoContent)
        :<|> (\key -> liftIO . STM.atomically $ do
                STM.modifyTVar' nodeState . CBCAST.send $ KvDel key
                return NoContent)
        :<|> (\key -> do
                kv <- liftIO $ STM.readTVarIO kvState
                maybe (throwError err404) return $ kvQuery key kv)
    nodeHandlers :: Server (ToServantApi PeerRoutes)
    nodeHandlers
        =    (\message -> liftIO . STM.atomically $ do
                STM.modifyTVar' nodeState $ CBCAST.receive message
                return NoContent)


-- ** Deliver messages

-- | Pop a deliverable message and apply it to application state.
-- TODO tests
readMail :: STM.TVar NodeState -> STM.TVar KvState -> STM.STM ()
readMail nodeState kvState = do
    message <- STM.stateTVar nodeState $ swap . CBCAST.deliver
    maybe STM.retry (STM.modifyTVar' kvState . kvApply . CBCAST.mRaw) message


-- ** Broadcast messages

-- | Drain broadcast messages and send them to peers. Does not return.
sendMailThread :: Peers -> STM.TVar NodeState -> IO ()
sendMailThread peers nodeState = do
    printf "sendMailThread will deliver to peers: %s\n" (unwords $ Servant.showBaseUrl <$> peers)
    connections <- HTTP.newManager HTTP.defaultManagerSettings
    let clientEnvs = Servant.mkClientEnv connections <$> peers
    peerQueues <- sequence $ replicate (length peers) STM.newTQueueIO
    -- Start tasks and wait forever.
    -- Note: Graceful shutdown is not implemented.
    printf "sendMailThread exited: %s\n" . show . snd
        =<< Async.waitAnyCatchCancel
        =<< mapM (Async.async . Monad.void . Monad.forever)
        ( feedPeerQueues nodeState peerQueues
        : (sendToPeer <$> zip clientEnvs peerQueues)
        )

-- | Copy all node broadcasts to all peer queues.
-- TODO tests
feedPeerQueues :: STM.TVar NodeState -> [STM.TQueue (Int, Broadcast)] -> IO ()
feedPeerQueues nodeState peerQueues = STM.atomically $ do
    messages <- STM.stateTVar nodeState $ swap . CBCAST.drainBroadcasts
    STM.check . not $ null messages -- TODO Check if we clock without this
    Monad.forM_ peerQueues $ \q ->
        Monad.forM_ messages $ \m ->
            STM.writeTQueue q (0, m)

-- | Send a message from a queue to a peer.
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
        peers <- mapM Servant.parseBaseUrl urls
        pid <- either fail return $ parsePID num peers
        let port = Servant.baseUrlPort $ peers !! pid
        printf "Starting KV server P%d on port %d with peer list: %s\n" pid port (unwords $ Servant.showBaseUrl <$> peers)
        nodeState <- STM.newTVarIO $ CBCAST.pNew pid (length peers)
        kvState <- STM.newTVarIO $ Map.empty
        -- Start tasks and wait forever.
        -- Note: Graceful shutdown is not implemented.
        printf "main thread exited: %s\n" . show . snd
            =<< Async.waitAnyCatchCancel
            =<< mapM Async.async
            [ Monad.forever . STM.atomically $ readMail nodeState kvState
            -- Note: sendMailThread does not receive the url of the current process.
            , sendMailThread (removeIndex pid peers) nodeState
            -- Note: Server listens on the port specified in the peer list.
            , Warp.run port $ handlers nodeState kvState
            ]


-- * Serialization Instances

instance Aeson.ToJSON KvCommand
instance Aeson.FromJSON KvCommand

deriving instance Generic CBCAST.VC
instance Aeson.ToJSON CBCAST.VC
instance Aeson.FromJSON CBCAST.VC

-- |
--
-- >>> let m = CBCAST.Message 1 (CBCAST.VC [1, 4]) (KvPut "some-key" Aeson.Null) :: Broadcast
-- >>> let m' = Aeson.decode $ Aeson.encode m :: Maybe Broadcast
-- >>> Just m == m'
-- True
--
-- >>> import Data.ByteString.Lazy.Char8 as BS
-- >>> BS.putStrLn $ Aeson.encode m'
-- {"mSender":1,"mRaw":{"tag":"KvPut","contents":["some-key",null]},"mSent":[1,4]}
--
deriving instance Generic r => Generic (CBCAST.Message r)
instance (Generic r, Aeson.ToJSON r) => Aeson.ToJSON (CBCAST.Message r)
instance (Generic r, Aeson.FromJSON r) => Aeson.FromJSON (CBCAST.Message r)


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
