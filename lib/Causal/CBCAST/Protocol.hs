{-# OPTIONS_GHC "-Wno-unused-imports" #-} -- LH needs listInitLast in scope
module Causal.CBCAST.Protocol where

import Redefined
import Causal.CBCAST.VectorClock
import Causal.CBCAST.Message
import Causal.CBCAST.DelayQueue
import Causal.CBCAST.Process


-- | Prepare to send a message (from this process to be broadcast on the
-- network). Return new process state.
--
--      "(1) Before sending m, process p_i increments VT(p_i)[i] and timestamps
--      m."
--
-- The copy of the message destined for delivery to the current process is
-- conveyed by a call to 'receive' here without passing through the network
-- (which would incur unbound delay) or the delay queue (which would be an
-- incorrect use).
--
{-@ reflect send @-}
send :: r -> Process r -> Process r
send r p
    = let
        vc = vcTick (pID p) (pVC p)
        m = Message{mSender=pID p, mSent=vc, mRaw=r}
    in receive m $ p
        { pVC = vc
        , pOutbox = fPush (pOutbox p) m
        }

-- | Receive a message (from the network to this process). Potentially delay
-- its delivery. Return new process state.
--
--      "(2) On reception of message m sent by p_i and timestamped with VT(m),
--      process p_j =/= p_i delays delivery of m until:
--
--          for-all k: 1...n { VT(m)[k] == VT(p_j)[k] + 1 if k == i
--                           { VT(m)[k] <= VT(p_j)[k]     otherwise
--
--      Process p_j need not delay messages received from itself. Delayed
--      messages are maintained on a queue, the CBCAST _delay queue_. This
--      queue is sorted by vector time, with concurrent messages ordered by
--      time of receipt (however, the queue order will not be used until later
--      in the paper)."
--
-- If the message was sent by the current process is it is put in a buffer for
-- immediate delivery.
--
{-@ reflect receive @-}
receive :: Message r -> Process r -> Process r
receive m p
    -- "Process p_j need not delay messages received from itself."
    | mSender m == pID p = p{pInbox=fPush (pInbox p) m}
    -- "Delayed messages are maintained on a queue, the CBCAST _delay queue_."
    | otherwise = p{pDQ=dqEnqueue m (pDQ p)}

-- | Deliver a message (from this process to the application). Return new
-- process state.
--
--      "(3) When a message m is delivered, VT(p_j) is updated in accordance
--      with the vector time protocol from Section 4.3."
--
-- The relevant part of section 4.3 is:
--
--      "(4) When process p_j delivers a message m from process p_i
--      containing VT(m), p_j modifies its vector clock in the
--      following manner:
--
--          for-all k element-of 1...n: VT(p_j)[k] = max(VT(p_j)[k], VT(m)[k])"
--
{-@ reflect internalDeliver @-}
internalDeliver :: Message r -> Process r -> Process r
internalDeliver m p = p
    { pVC = vcCombine (pVC p) (mSent m)
    }

-- | Remove and return all sent messages so the application can broadcast them
-- (in sent-order, eg, with 'foldl'' or 'mapM_').
{-@ reflect drainBroadcasts @-}
drainBroadcasts :: Process r -> (Process r, [Message r])
drainBroadcasts p =
    ( p{pOutbox=fNew}
    , fList (pOutbox p)
    )

-- | Return the next message ready for delivery by checking first for messages
-- sent by the current process and second for deliverable messages in the delay
-- queue.
{-@ reflect deliver @-}
deliver :: Process r -> (Process r, Maybe (Message r))
deliver p = case fPop (pInbox p) of
    Just (m, inbox) -> (internalDeliver m p{pInbox=inbox}, Just m)
    Nothing -> case dqDequeue (pVC p) (pDQ p) of
        Just (dq, m) -> (internalDeliver m p{pDQ=dq}, Just m)
        Nothing -> (p, Nothing)
