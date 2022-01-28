{-@ LIQUID "--ple" @-}
{-# LANGUAGE NamedFieldPuns #-}
module UCausalDelivery where

import Language.Haskell.Liquid.ProofCombinators

import Redefined.List -- (listLength, listAnd, listZipWith, listZipWith3) -- PLE needs everything in scope
import Redefined.Bool -- PLE needs everything in scope
import Redefined.Fin (fin)
import Redefined.Ord (ordMax)
import Redefined.Proof (proofConst)


-- * Vector clocks

type Clock = Integer

type VC = [Clock]

{-@ reflect vcLessEqual @-}
vcLessEqual :: VC -> VC -> Bool
vcLessEqual a b = listAnd (listZipWith vcLessEqualHelper a b)
{-@ reflect vcLessEqualHelper @-}
vcLessEqualHelper :: Clock -> Clock -> Bool
vcLessEqualHelper a b = a <= b

{-@ reflect vcLess @-}
vcLess :: VC -> VC -> Bool
vcLess a b = a `vcLessEqual` b && a /= b

{-@ reflect vcConcurrent @-}
vcConcurrent :: VC -> VC -> Bool
vcConcurrent a b = not (a `vcLess` b) && not (b `vcLess` a)


-- * Message

type PID = Int

{-@
data M = M {sender::PID, vc_m::VC, msg::String} @-}
data M = M {sender::PID, vc_m::VC, msg::String}

{-@ reflect ===> @-}
(===>) :: M -> M -> Bool
M{vc_m=a} ===> M{vc_m=b} = a `vcLess` b

-- | A convenience alias.
{-@ reflect <=== @-}
(<===) :: M -> M -> Bool
a <=== b = b ===> a

{-@ reflect |||| @-}
(||||) :: M -> M -> Bool
M{vc_m=a} |||| M{vc_m=b} = a `vcConcurrent` b


-- * Deliverable predicate

{-@ reflect deliverable @-}
deliverable :: M -> VC -> Bool
deliverable M{sender=i, vc_m} vc_p =
    let n = listLength vc_m `ordMax` listLength vc_p
    in listAnd (listZipWith3 (deliverableHelper i) (fin n) vc_m vc_p)
{-@ reflect deliverableHelper @-}
deliverableHelper :: PID -> PID -> Clock -> Clock -> Bool
deliverableHelper i k vc_m_k vc_p_k -- i is sender, k is current.
    | k == i    = vc_m_k == vc_p_k + 1
    | otherwise = vc_m_k <= vc_p_k


-- * Delay queue

type DQ = [M]

{-@ reflect enqueue @-}
enqueue :: M -> DQ -> DQ
enqueue m [] = [m]
enqueue m (x:xs)
    | m ===> x  = m:x:xs -- Messages are in order of their vector clocks.
    | m |||| x  = x:enqueue m xs -- Concurrent messages are in receipt order.
    | otherwise = x:enqueue m xs

{-@ reflect dequeue @-}
dequeue :: VC -> DQ -> Maybe (M, DQ)
dequeue _now [] = Nothing
dequeue now (x:xs)
    | deliverable x now = Just (x, xs)
    | otherwise =
        case dequeue now xs of -- Skip past x.
            Nothing -> Nothing
            Just (m, xs') -> Just (m, x:xs')


-- * Tick

{-@ reflect tick @-}
tick :: PID -> VC -> VC
tick pid now | pid < 0 = now
tick _pid [] = []
tick 0 (x:xs) = (x + 1) : xs
tick pid (x:xs) = x : tick (pid - 1) xs
-- let (xs, y:ys) = listSplitAt pid now
-- in xs++(y + 1):ys



{-@
data P = P {pid::PID, vc_p::VC, dq::DQ} @-}
data P = P {pid::PID, vc_p::VC, dq::DQ}

-- | Put a message in the dq.
{-@ reflect receive @-}
receive :: M -> P -> P
receive m P{pid,vc_p,dq} =
    P{pid,vc_p,dq=enqueue m dq}

-- | Get a message from the dq and update the local VC.
{-@ reflect deliver @-}
deliver :: P -> Maybe (M, P)
deliver P{pid,vc_p,dq} =
    case dequeue vc_p dq of
        Nothing -> Nothing
        Just (m@M{vc_m}, dq') ->
            let vc_p' = listZipWith ordMax vc_p vc_m -- Could use tick here.
            in Just (m, P{pid, vc_p=vc_p', dq=dq'})

-- | Prepare a message for broadcast.
--
-- Must also convey M to this process via receive and then deliver, in that way
-- updating the local process VC. You can do this by sending over the network,
-- but that's not advised.
{-@ reflect broadcast @-}
broadcast :: String -> P -> M
broadcast msg P{pid,vc_p} =
    let vc_m = tick pid vc_p
    in M{sender=pid, vc_m, msg}

-- | Prepare a message for broadcast, put it into this process's delay queue,
-- and then perform a normal delivery.
{-@ reflect broadcastCycle @-}
broadcastCycle :: String -> P -> (M, P)
broadcastCycle msg p =
    case deliver (receive (broadcast msg p) p)
    `proofConst` broadcastCycleAlwaysDelivers msg p of
        Just tup -> tup

-- -- {-@
-- -- broadcastIs :: msg:_ -> p:_ -> {} @-}
-- 
-- {-@
-- broadcastIsDeliverable :: msg:_ -> p:_ -> {deliverable (broadcast msg p) (vc_p p)} @-}
-- broadcastIsDeliverable :: String -> P -> Proof
-- broadcastIsDeliverable msg p@P{vc_p}
--     =   deliverable (broadcast msg p) (vc_p p)
--     *** Admit

{-@
broadcastCycleAlwaysDelivers :: msg:_ -> p:_ -> {Nothing /= deliver (receive (broadcast msg p) p)} @-}
broadcastCycleAlwaysDelivers :: String -> P -> Proof
broadcastCycleAlwaysDelivers msg p = () *** Admit
-- ? broadcastIsDeliverable msg p
