{-# OPTIONS_GHC "-Wno-unused-imports" #-} -- LH needs bodies of reflected definitions
{-# OPTIONS_GHC "-Wno-warnings-deprecations" #-} -- Hide the "verification only" and "internal use" warnings
{-# LANGUAGE GADTs #-}

module CBCAST.Verification.NetworkSemantics {-# WARNING "Verification only" #-} where

import Language.Haskell.Liquid.ProofCombinators
import Language.Haskell.Liquid.ProofCombinatorsExtra (proofConst)

import Redefined
import CBCAST.Core
import CBCAST.Step
import CBCAST.Transitions
import CBCAST.Verification.PLCDpresStep (stepShim)




-- | An execution is a mapping from process identifier to CBCAST processes. The
-- mapping is constrained to only those processes /in/ the execution by the
-- size parameter, @N@.
type Execution r = PID -> Process r
{-@ type Xsized r N = p_id_k:PIDsized {N} -> {p_v:Psized r {N} | p_id_k == pID p_v} @-}
---- QQQ Xsized breaks setProcess b/c of name collisions again. Repro5, issue #2017

{-@
setProcess :: n:Nat -> p_id:PIDsized {n} -> {p:Psized r {n} | p_id == pID p} -> Xsized r {n} -> Xsized r {n} @-}
setProcess :: Int -> PID -> Process r -> Execution r -> Execution r
setProcess _n k v mapping target
    | target == k = v
    | otherwise = mapping target

{-@
setProcess2 :: n:Nat -> Psized r {n} -> Xsized r {n} -> Xsized r {n} @-}
setProcess2 :: Int -> Process r -> Execution r -> Execution r
setProcess2 n p = setProcess n (pID p) p




-- | A packet is a unicast message with source and destination fields.
data Packet id m = Packet {pSrc::id, pDst::id, pMsg::m}
    deriving Eq

-- | A "packets" is a list of (src, dst, msg) tuples constrained to have
-- compatible vector clocks by the size parameter, @N@.
type Packets r = [Packet PID (Message r)]
{-@ type PKsized r N = [Packet (PIDsized {N}) (Msized r {N})] @-}

-- | A net is the global state of communicating CBCAST processes, containing
-- unicast packets inflight, an execution, and constrained to have compatible
-- vector clocks by the size field, @nN@.
{-@
data Net r = Net {nN::Nat, nPackets::PKsized r {nN}, nExecution::Xsized r {nN}} @-}
data Net r = Net {nN::Int, nPackets::Packets r, nExecution::Execution r}
{-@ type Nsized r N = {sizedN:Net r | nN sizedN == N} @-}




-- | Is the op ok to use with xStep?
--
-- RECEIVE: There's a packet. Packet is for p_id and is from sender of
-- Receive's message and contains Receive's message.
--
-- DELIVER: The process has a deliverable message.
--
-- BROADCAST: No preconditions.
--
{-@ inline opPrecond @-} -- Required for fewer cases in xStep
{-@
opPrecond :: nt:Net r -> PIDsized {nN nt} -> OPsized r {nN nt} -> Bool @-}
opPrecond :: Eq r => Net r -> PID -> Op r -> Bool
opPrecond Net{nPackets=k:_ks} p_id (OpReceive _n m@Message{mSender=mSrc}) =
    k == Packet{pSrc=mSrc,pDst=p_id,pMsg=m}
opPrecond _net _p_id OpReceive{} = False
opPrecond Net{nExecution=x} p_id op@OpDeliver{} =
    case step op (x p_id) of ResultDeliver _ Just{} -> True; ResultDeliver _ Nothing -> False
opPrecond _net _p_id OpBroadcast{} = True

-- WARNING: (lib/CBCAST/Verification/NetworkSemantics.hs:(85,1)-(95,41)) Not
-- expanding DEFAULT with 2 cases at depth 4
{-@ LIQUID "--max-case-expand=5" @-}

-- | Step forward an execution.
{-@
xStep :: nt:Net r -> p_id:PIDsized {nN nt} -> {op:OPsized r {nN nt} | opPrecond nt p_id op} -> Nsized r {nN nt} @-}
xStep :: Net r -> PID -> Op r -> Net r
-- Receive packet _k, already known to be addressed to p_id, and matching both
-- sender and content of message in OpReceive. Update process and packets.
xStep (Net n (_k:ks') x) p_id op@OpReceive{} =
    let ResultReceive _n p = step op (x p_id)
        x' = setProcess2 n p x
    in Net n ks' x'
-- Deliver a message. Update process. (Not tracked: The message isn't applied
-- to some local application state.)
xStep (Net n ks x) p_id op@OpDeliver{} =
    let ResultDeliver _n (Just (_m, p)) = step op (x p_id)
        x' = setProcess2 n p x
    in Net n ks x'
-- Broadcast a message. Update process and packets. (Not tracked: The message
-- isn't applied to some local application state.)
xStep (Net n ks x) p_id op@OpBroadcast{} =
    let ResultBroadcast _n (m, p) = step op (x p_id)
        x' = setProcess2 n p x
        ks' = broadcastPackets n p_id (finDesc n) m
    in Net n (ks +++ ks') x'

-- | Packets for addressed to all but the sender.
{-@
broadcastPackets :: n:Nat -> PIDsized {n} -> [PIDsized {n}] -> Msized r {n} -> PKsized r {n} @-}
broadcastPackets :: Int -> PID -> [PID] -> Message r -> Packets r
broadcastPackets _n _src     []     _msg = []
broadcastPackets  n  src (dst:dsts)  msg
    | src == dst =                                         broadcastPackets n src dsts msg
    | otherwise  = Packet {pSrc=src, pDst=dst, pMsg=msg} : broadcastPackets n src dsts msg
{-@ reflect broadcastPackets @-}

-- | Reflected list-append.
(+++) :: [a] -> [a] -> [a]
[] +++ ys = ys
(x:xs) +++ ys = x : (xs +++ ys)
{-@ infixr 5 +++ @-}
{-@ reflect +++ @-}
