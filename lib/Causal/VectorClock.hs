module Causal.VectorClock where

import Redefined

import Data.UUID (UUID, fromWords)

face :: UUID
face = fromWords 0xface 0xface 0xface 0xface

cafe :: UUID
cafe = fromWords 0xcafe 0xcafe 0xcafe 0xcafe

-- reflect can't handle UUID
-- inline can handle UUID

-- clocks start from 0
--  * when pid not in the list, the value of a clock is 0
--  * when pid is in the list, the value of a clock is 1..

type Clock = Integer
{-@ type Clock = {c:Integer | 0 <= c} @-}


{-@ type VCFun pid = pid -> Clock @-}
type VCFun pid = pid -> Clock

{-@ vcfNew :: VCFun pid @-}
vcfNew :: VCFun pid
vcfNew _ = 0
{-@ inline vcfNew @-}

{-@ vcfTick :: Eq pid => pid -> VCFun pid -> VCFun pid @-}
vcfTick :: Eq pid => pid -> VCFun pid -> VCFun pid
vcfTick incPid vc lookupPid
    | incPid == lookupPid = vc lookupPid + 1
    | otherwise = vc lookupPid
{-@ inline vcfTick @-}


{-@ type Unique a = [a]<{\x y -> x /= y}> @-}

{-@ uInsert :: a -> Unique a -> Unique a @-}
uInsert :: Eq a => a -> [a] -> [a]
uInsert x [] = x : []
uInsert x (y:ys)
    | x == y = y:ys
    | otherwise = y:uInsert x ys
{-@ reflect uInsert @-}


type VCWrapper pid = (VCFun pid, [pid])
{-@ type VCWrapper pid = (VCFun pid, Unique pid) @-}

{-@ vcwNew :: VCWrapper pid @-}
vcwNew :: VCWrapper pid
vcwNew = (vcfNew, [])

{-@ vcwTick :: Eq pid => pid -> VCWrapper pid -> VCWrapper pid @-}
vcwTick :: Eq pid => pid -> VCWrapper pid -> VCWrapper pid
vcwTick pid (fun, pids) = (vcfTick pid fun, uInsert pid pids)
