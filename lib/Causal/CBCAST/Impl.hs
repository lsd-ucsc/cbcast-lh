module Causal.CBCAST.Impl where

import Causal.VectorClock
import Causal.CBCAST.Message
import Causal.CBCAST.DelayQueue
import Causal.CBCAST.Process


-- * Implementation


-- ** Internal operations

-- | Prepare to send a message (from this process to be broadcast on the
-- network).  Return new process state.
--
--      "(1) Before sending m, process p_i increments VT(p_i)[i] and timestamps
--      m."
--
-- Since this modifies the vector clock, it could change the deliverability of
-- messages in the delay queue. Therefore 'internalDeliverReceived' must be run
-- after this.
internalSend :: r -> Process r -> Process r
internalSend r p = let vt = vcTick (pNode p) (pVT p) in p
    { pVT = vt
    , pOutbox = fPush (pOutbox p) Message{mSender=pNode p, mSent=vt, mRaw=r}
    -- FIXME: message to self should be placed directly in the inbox
    -- FIXME: message to self must be delivered directly to self without passing through DQ
    -- FIXME: message to self must not go on the network; if it _does_ go on the network it must be specially handled upon receipt so as not to go on the delay queue
    }
{-@ inline internalSend @-}

-- | Receive a message (from the network to this process). Delay its delivery
-- or deliver it immediately. The "until" part is handled by
-- 'internalDeliverReceived'. Return new process state.
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
-- Since this modifies the vector clock in one case and the delay queue in the
-- other, it could change the deliverability of messages in the delay queue.
-- Therefore 'internalDeliverReceived' must be run after this.
internalReceive :: Message r -> Process r -> Process r
internalReceive m p
    -- "Process p_j need not delay messages received from itself."
    | mSender m == pNode p = internalDeliver m p
    -- "Delayed messages are maintained on a queue, the CBCAST _delay queue_."
    | otherwise = p{pDQ=dqEnqueue m (pDQ p)}
{-@ inline internalReceive @-}

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
-- Since this modifies the vector clock, it could change the deliverability of
-- messages in the delay queue. Therefore 'internalDeliverReceived' must be run
-- after this.
{-@
internalDeliver :: _ -> p:_ -> {p':_ | pdqSize p == pdqSize p' } @-}
internalDeliver :: Message r -> Process r -> Process r
internalDeliver m p = p
    { pVT = vcCombine (pVT p) (mSent m)
    , pInbox = fPush (pInbox p) m
    }
{-@ inline internalDeliver @-}

-- | Deliver messages until there are none ready.
--
-- This algorithm delivers full groups of deliverable messages before checking
-- deliverability again. While this can't make anything undeliverable or break
-- causal order of deliveries, it does produce a slightly different delivery
-- order than an algorithm which checks deliverability after every delivery.
{-@
internalDeliverReceived :: p:_ -> _ / [pdqSize p] @-}
internalDeliverReceived :: Process r -> Process r
internalDeliverReceived p =
    case dqDequeue (pVT p) (pDQ p) of
        Just (dq, m) -> internalDeliverReceived (internalDeliver m p{pDQ=dq})
        Nothing -> p
{-@ reflect internalDeliverReceived @-}


-- ** External API

-- | Prepare a message for sending, possibly triggering the delivery of
-- messages in the delay queue.
send :: r -> Process r -> Process r
send r p = internalDeliverReceived $ internalSend r p
-- FIXME: message to self must be delivered directly to self without passing through DQ
{-@ inline send @-}

-- | Receive a message, possibly triggering the delivery of messages in the
-- delay queue.
receive :: Message r -> Process r -> Process r
receive m p = internalDeliverReceived $ internalReceive m p
{-@ inline receive @-}

-- | Remove and return all sent messages so the application can broadcast them
-- (in sent-order, eg, with 'mapM_').
drainBroadcasts :: Process r -> (Process r, [Message r])
drainBroadcasts p =
    ( p{pOutbox=fNew}
    , fList (pOutbox p)
    )
{-@ inline drainBroadcasts @-}

-- | Remove and return all delivered messages so the application can process
-- them (in delivered-order, eg, with 'fmap').
drainDeliveries :: Process r -> (Process r, [Message r])
drainDeliveries p =
    ( p{pInbox=fNew}
    , fList (pInbox p)
    )
{-@ inline drainDeliveries @-}
