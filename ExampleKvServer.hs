{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DeriveGeneric #-}
module Main where

import qualified Data.Aeson as JSON

import qualified Causal.CBCAST.VectorClock as CBCAST
import qualified Causal.CBCAST.Message as CBCAST

import Network.HTTP.Types.Method -- Does not resolve LH issue
import Servant
import Servant.API.Generic

type Key = String
type Val = JSON.Value

data AppCast
    = Set Key Val
    | Del Key

type CBCAST = CBCAST.Message AppCast

data Routes mode = Routes
    { kvGet :: mode :- "kv" :> Capture "key" Key :> Get '[JSON] Val -- Triggers LH issue
    , kvPut :: mode :- "kv" :> Capture "key" Key :> ReqBody '[JSON] Val :> PutNoContent
    , kvDel :: mode :- "kv" :> Capture "key" Key :> DeleteNoContent
    , cbcast :: mode :- "cbcast" :> ReqBody '[JSON] CBCAST :> PostNoContent
    }
    deriving (Generic)

main :: IO ()
main = print "example not implemented"
