{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DeriveGeneric #-}
module Main where

import qualified Data.Aeson as Aeson

import qualified Causal.CBCAST.VectorClock as CBCAST
import qualified Causal.CBCAST.Message as CBCAST

import Servant
import Servant.API.Generic ((:-), Generic, ToServantApi)
-- import Servant.Server.Generic

-- * Types for clients

type Key = String
type Val = Aeson.Value

data ClientRoutes mode = ClientRoutes
    { kvGet :: mode :- "kv" :> Capture "key" Key :> Get '[JSON] Val
    , kvPut :: mode :- "kv" :> Capture "key" Key :> ReqBody '[JSON] Val :> PutNoContent
    , kvDel :: mode :- "kv" :> Capture "key" Key :> DeleteNoContent
    }
    deriving (Generic)

-- * Types for servers

data AppCast
    = Set Key Val
    | Del Key

type CBCAST = CBCAST.Message AppCast

data ServerRoutes mode = ServerRoutes
    { cbcast :: mode :- "cbcast" :> ReqBody '[JSON] CBCAST :> PostNoContent
    }
    deriving (Generic)

serverWaiApp :: Application
serverWaiApp = undefined {- serve
    (Proxy :: Proxy (ToServantApi ClientRoutes :<|> ToServantApi ServerRoutes))
    (clientServer :<|> serverServer) -}
  where
    -- https://github.com/haskell-servant/servant/issues/1394
    clientServer :: Server (ToServantApi ClientRoutes)
    clientServer
        =    (\key -> return undefined)
        :<|> (\key -> return undefined)
        :<|> (\key -> return undefined)
    serverServer :: Server (ToServantApi ServerRoutes)
    serverServer
        =    (\message -> return undefined)

main :: IO ()
main = print "example not implemented"
