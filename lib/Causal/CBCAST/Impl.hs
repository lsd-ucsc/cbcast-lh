

module Causal.CBCAST.Impl
( pNew
, send
, receive
, drainBroadcasts
, drainDeliveries
) where

-- page 7/278:
--
--      "The execution of a process is a partial ordered sequence of _events_,
--      each corresponding to the execution of an indivisible action. An
--      acyclic event order, denoted ->^p, reflects the dependence of events
--      occuring at process p upon one another."
--
--      "As Lamport [17], we define the potential causality relation for the
--      system, ->, as the transitive closure of the relation defined as
--      follows:
--
--      (1) if there-exists p: e ->^p e' then e -> e'
--      (2) for-all m: send(m) -> rcv(m)"
--
-- page 8/279:
--
--      "Two types of delivery ordering will be of interest here. We define the
--      causal delivery ordering for multicast messages m and m' as follows:
--
--          m -> m' => for-all p element-of dests(m) intersect dests(m'):
--                      deliver(m) ->^p deliver(m')
--
--      CBCAST provides only th ecausal delivery ordering."
--
-- page 10/281:
--
--      "Suppose that a set of processes P communicate using only broadcasts to
--      the full set of processes in the system; that is,
--      for-all m: dests(m) = P."
--
--      "We now develop a _delivery protocol_ by which each process p receives
--      messages sent to it, delays them if necessary, and then delivers them
--      in an order consistent with causality:
--
--          m -> m' => for-all p: deliver_p(m) ->^p deliver_p(m')

import Causal.CBCAST.DelayQueue
import Causal.CBCAST.Message
import Causal.CBCAST.Process
import Causal.VectorClockConcrete

-- * Implementation

-- ** Internal operations

-- | Prepare to send a message. Return new process state.
--
--      "(1) Before sending m, process p_i increments VT(p_i)[i] and timestamps
--      m."
--
-- Since this modifies the vector clock, it could change the deliverability of
-- messages in the delay queue. Therefore 'cbcastDeliverReceived' must be run
-- after this.
cbcastSend :: r -> Process r -> Process r
cbcastSend r p = let vt = vcTick (pNode p) (pVT p) in p
    { pVT = vt
    , pOutbox = fPush (pOutbox p) Message{mSender=pNode p, mSent=vt, mRaw=r}
    }

-- | Receive a message. Delay its delivery or deliver it immediately. The
-- "until" part is handled by 'cbcastDeliverReceived'. Return new process
-- state.
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
-- Therefore 'cbcastDeliverReceived' must be run after this.
cbcastReceive :: Message r -> Process r -> Process r
cbcastReceive m p
    -- "Process p_j need not delay messages received from itself."
    | mSender m == pNode p = cbcastDeliver m p
    -- "Delayed messages are maintained on a queue, the CBCAST _delay queue_."
    | otherwise = p{pDQ=dqEnqueue m (pDQ p)}

-- | Deliver messages until there are none ready.
cbcastDeliverReceived :: Process r -> Process r
cbcastDeliverReceived p = case dqDequeue (pVT p) (pDQ p) of
    Just (dq, m) -> cbcastDeliverReceived (cbcastDeliver m p{pDQ=dq})
    Nothing -> p

-- | Deliver a message. Return new process state.
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
-- messages in the delay queue. Therefore 'cbcastDeliverReceived' must be run
-- after this.
cbcastDeliver :: Message r -> Process r -> Process r
cbcastDeliver m p = p
    { pVT = vcCombine (pVT p) (mSent m)
    , pInbox = fPush (pInbox p) m
    }

-- ** External API

-- | Prepare a message for sending, possibly triggering the delivery of
-- messages in the delay queue.
send :: r -> Process r -> Process r
send r = cbcastDeliverReceived . cbcastSend r

-- | Receive a message, possibly triggering the delivery of messages in the
-- delay queue.
receive :: Message r -> Process r -> Process r
receive m = cbcastDeliverReceived . cbcastReceive m

-- | Remove and return all sent messages so the application can broadcast them
-- (in sent-order, eg, with 'mapM_').
drainBroadcasts :: Process r -> (Process r, [Message r])
drainBroadcasts p =
    ( p{pOutbox=fNew}
    , fList (pOutbox p)
    )

-- | Remove and return all delivered messages so the application can process
-- them (in delivered-order, eg, with 'fmap').
drainDeliveries :: Process r -> (Process r, [Message r])
drainDeliveries p =
    ( p{pInbox=fNew}
    , fList (pInbox p)
    )

-- * Verification

{-@ cbcastDeliverReceived :: x:Process r -> Process r / [pdqSize x] @-}
