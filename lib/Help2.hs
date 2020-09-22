{-# LANGUAGE QuasiQuotes #-}
module Help2 where

import LiquidHaskell (lq)

import Help

{-@
data UseOfEg [useOfEgLen] = UseOfEg Eg @-}
data UseOfEg              = UseOfEg Eg

[lq|
useOfEgLen :: UseOfEg -> Int |]
useOfEgLen (UseOfEg eg) = egLen eg
{-@ measure useOfEgLen @-}
