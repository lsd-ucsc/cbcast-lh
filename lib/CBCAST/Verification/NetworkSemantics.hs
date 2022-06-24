{-# LANGUAGE GADTs #-}

module CBCAST.Verification.NetworkSemantics {-# WARNING "Verification only" #-} where

import CBCAST.Core
import CBCAST.Transitions

-- | An execution is a mapping from process identifier to CBCAST processes. The
-- mapping is constrained to only those processes /in/ the execution by the
-- size parameter, @N@.
type Execution r = PID -> Process r
{-@ type Xsized r N = p_id:PIDsized {N} -> {p:Psized r {N} | p_id == pID p} @-}

-- | A packet is a unicast message with source and destination fields.
data Packet id m = Packet {pSrc::id, pDst::id, pMsg::m}

-- | A "packets" is a list of (src, dst, msg) tuples constrained to have
-- compatible vector clocks by the size parameter, @N@.
type Packets r = [Packet PID (Message r)]
{-@ type PKsized r N = [Packet (PIDsized {N}) (Msized r {N})] @-}

-- | A net is the global state of communicating CBCAST processes, containing
-- unicast packets inflight, an execution, and constrained to have compatible
-- vector clocks by the size field, @wN@.
-- {-@
-- data Net r = Net {wN::Nat, wPackets::PKsized r {wN}, wExecution::Xsized r {wN}} @-}
-- data Net r = Net {wN::Int, wPackets::Packets r, wExecution::Execution r}
type Net r = (Packets r, Execution r)
{-@ type Net r N = (PKsized r {N}, Xsized r {N}) @-}
-- QQQ We might run into a problem because this type alias `Net r N` is not
-- used anywhere, and so the packets and execution aren't actually constrained
-- to be compatible.

-- | Network transition-relation propositions.
data NetProp r where (:~~>) :: Net r -> Net r -> NetProp r
{-@ infix :~~> @-}

-- | Nicer syntax for (:~~>).
(~>) :: Net r -> Net r -> NetProp r
a ~> b = a :~~> b
{-@ infix ~> @-}
{-@ reflect ~> @-}
-- QQQ the use of reflection for ~> (instead of inline) might
-- break LH's reasoning.

-- | Reflected list-cons. (Constructor only needs infix annotation)
{-@ infixr 5 : @-}

-- | Reflected list-append.
(+++) :: [a] -> [a] -> [a]
[] +++ ys = ys
(x:xs) +++ ys = x : (xs +++ ys)
{-@ infixr 5 +++ @-}
{-@ reflect +++ @-}

{-@ zzz :: a:_ -> b:_ -> Prop{ a ~> b } @-}
zzz :: Net r -> Net r -> NetProp r
zzz _ _ = undefined

data NetRule r where
    Send ::
        Packets r -> Execution r -> -- relation inputs
        r -> PID ->                 -- send inputs
        Message r -> Process r ->   -- send outputs
        Packets r -> Execution r -> -- relation outputs
        NetRule r
    Deliver :: NetRule r
    Receive :: NetRule r
    Permute :: NetRule r
-- We use
--  k for P (pacKets)
--  x for Σ (eXecution)
--  src, dst, and pid for PIDs
--      (reserving n for the future, in case we need to specify vc size)
--  r for a raw message value
--  σ for a single Process state
{-@
data NetRule r where
    Send ::
        k:_ -> x:_ ->
        r:_ -> src:_ ->
        m:_ -> {σ:_ | (m, σ) == internalBroadcast r (x src) } ->
        {k':_ | true } ->
        {x':_ | true } ->
        Prop{ (k, x) ~> (k +++ k', x') }
    Deliver :: NetRule r
    Receive :: NetRule r
    Permute :: NetRule r
@-}
