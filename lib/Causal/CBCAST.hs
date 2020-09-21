{-# LANGUAGE QuasiQuotes #-}
{-|
Description: Proof of a causal delivery property.
-}
module Causal.CBCAST where

-- page 7/278:
--
--      "The execution of a process is a partiall ordered sequence of _events_,
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

import LiquidHaskell (lq)

import Causal.CBCAST.Message (PID, VT, Message(..))
import Causal.CBCAST.DelayQueue
import Causal.VectorClockConcrete

-- | Prepare a message for sending, possibly triggering the delivery of
-- messages in the delay-queue. Callers are responsible for broadcasting the
-- packaged message and then processing their results from any deliveries which
-- may occurred.
send :: Accept r res -> r -> Process r -> (Process r, Message r, [res])
send uAccept r p = (p'', m, res)
  where
    (p', m) = cbcastSend r p
    (p'', res) = deliveryLifecycle uAccept p'

-- | Receive a message, possibly triggering the delivery of messages in the
-- delay-queue. Callers are responsible for processing the results from any
-- deliveries which may have occurred.
receive :: Accept r res -> Message r -> Process r -> (Process r, [res])
receive uAccept m p = fmap (maybe id (:) res) (deliveryLifecycle uAccept p')
  where
    (p', res) = cbcastReceive uAccept m p

-- | Deliver messages until there are none ready.
[lq|
deliveryLifecycle :: Accept r res -> Process r -> (Process r, [res]) |]
deliveryLifecycle uAccept p = case dqDequeue (pVT p) (pDQ p) of
    Just (dq', m) ->
        let (p', res) = cbcastDeliver uAccept m p{pDQ=dq'}
        in fmap (res:) (deliveryLifecycle uAccept p')
    Nothing -> (p, [])

-----------------

type DQ r = DelayQueue r

data Process r = Process { pNode :: PID, pVT :: VT, pDQ :: DQ r}

-- | User function. Accept a message with metadata and return some result which
-- orchestration hands back to the user code. Results from multiple deliveries
-- will be returned in-order, and so it makes sense to return a monadic result
-- and then use 'sequence' to process them in the correct order.
type Accept r res = Message r -> res

-- | Prepare to send a message. Return new process state and timestamped
-- message.
--
--      "(1) Before sending m, process p_i increments VT(p_i)[i] and timestamps
--      m."
--
-- Since this modifies the vector-clock and could change the deliverability of
-- messages in the delay-queue, the delivery lifecycle must be run after this.
cbcastSend :: r -> Process r -> (Process r, Message r)
cbcastSend r p = (p{pVT=vt'}, Message{mSender=pNode p, mSent=vt', mRaw=r})
  where
    vt' = vcTick (pNode p) (pVT p)

-- | Receive a message. Delay its delivery on a queue or deliver it
-- immediately. Return new process state. The "until" part is handled by
-- 'deliveryLifecycle'.
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
-- Since this modifies the vector-clock in one case and the delay-queue in the
-- other, it could change the deliverability of messages in the delay-queue,
-- the delivery lifecycle must be run after this.
cbcastReceive :: Accept r res -> Message r -> Process r -> (Process r, Maybe res)
cbcastReceive uAccept m p
    -- "Process p_j need not delay messages received from itself."
    | mSender m == pNode p = fmap pure (cbcastDeliver uAccept m p)
    -- "Delayed messages are maintained on a queue, the CBCAST _delay queue_."
    | otherwise = (p{pDQ=dqEnqueue m (pDQ p)}, Nothing)

-- | Deliver a message by calling a user supplied function. Return new process
-- state and user delivery result.
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
-- Since this modifies the vector-clock and could change the deliverability of
-- messages in the delay-queue, the delivery lifecycle must be run after this.
cbcastDeliver :: Accept r res -> Message r -> Process r -> (Process r, res)
cbcastDeliver uAccept m p = (p{pVT=vt'}, uAccept m)
  where
    vt' = vcCombine (pVT p) (mSent m)
