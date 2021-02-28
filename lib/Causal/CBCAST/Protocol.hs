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
--
-- >>> pNew 0 2
-- Process {pID = 0, pVC = VC [0,0], pDQ = DelayQueue [], pToSelf = FIFO [], pToNetwork = FIFO []}
--
-- >>> send "hello" $ pNew 0 2
-- Process {pID = 0, pVC = VC [1,0], pDQ = DelayQueue [], pToSelf = FIFO [...VC [1,0]...], pToNetwork = FIFO [...VC [1,0]...]}
--
{-@ reflect send @-}
send :: r -> Process r -> Process r
send r p
    = let
        vc = vcTick (pID p) (pVC p)
        m = Message{mSender=pID p, mSent=vc, mRaw=r}
    in receive m $ p
        { pVC = vc
        , pToNetwork = fPush (pToNetwork p) m
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
--
-- >>> pNew 0 2
-- Process {pID = 0, pVC = VC [0,0], pDQ = DelayQueue [], pToSelf = FIFO [], pToNetwork = FIFO []}
--
-- Receive from self:
--
-- >>> let msgSelf = Message 0 (VC [1,0]) "hello"
-- >>> receive msgSelf $ pNew 0 2
-- Process {pID = 0, pVC = VC [0,0], pDQ = DelayQueue [], pToSelf = FIFO [...VC [1,0]...], pToNetwork = FIFO []}
--
-- Receive from other:
--
-- >>> let msgOther = Message 1 (VC [0,1]) "world"
-- >>> receive msgOther $ pNew 0 2
-- Process {pID = 0, pVC = VC [0,0], pDQ = DelayQueue [...VC [0,1]...], pToSelf = FIFO [], pToNetwork = FIFO []}
--
{-@ reflect receive @-}
receive :: Message r -> Process r -> Process r
receive m p
    -- "Process p_j need not delay messages received from itself."
    | mSender m == pID p = p{pToSelf=fPush (pToSelf p) m}
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

-- | Return the next message ready for delivery by checking first for messages
-- sent by the current process and second for deliverable messages in the delay
-- queue.
--
-- >>> pNew 0 2
-- Process {pID = 0, pVC = VC [0,0], pDQ = DelayQueue [], pToSelf = FIFO [], pToNetwork = FIFO []}
--
-- >>> let (p, m) = deliver $ pNew 0 2
-- >>> p == pNew 0 2 && m == Nothing
-- True
--
-- >>> let msgSelf = Message 0 (VC [1,0]) "hello"
-- >>> let msgOther = Message 1 (VC [0,1]) "world"
-- >>> receive msgOther . receive msgSelf $ pNew 0 2
-- Process {pID = 0, pVC = VC [0,0], pDQ = DelayQueue [...], pToSelf = FIFO [...], pToNetwork = FIFO []}
--
-- Deliver once: Messages from self take priority. VC is updated.
--
-- >>> let (p, m) = deliver . receive msgOther . receive msgSelf $ pNew 0 2
-- >>> p
-- Process {pID = 0, pVC = VC [1,0], pDQ = DelayQueue [...], pToSelf = FIFO [], pToNetwork = FIFO []}
-- >>> m == Just msgSelf
-- True
--
-- Deliver twice: Messages from other may be delivered. VC is updated.
--
-- >>> let (p, m) = deliver . fst . deliver . receive msgOther . receive msgSelf $ pNew 0 2
-- >>> p
-- Process {pID = 0, pVC = VC [1,1], pDQ = DelayQueue [], pToSelf = FIFO [], pToNetwork = FIFO []}
-- >>> m == Just msgOther
-- True
--
-- Deliver when others' message not deliverable:
--
-- >>> let (p, m) = deliver . receive (Message 1 (VC [0,1,1]) "future") $ pNew 0 3
-- >>> p
-- Process {pID = 0, pVC = VC [0,0,0], pDQ = DelayQueue [...], pToSelf = FIFO [], pToNetwork = FIFO []}
-- >>> m == Nothing
-- True
--
{-@ reflect deliver @-}
deliver :: Process r -> (Process r, Maybe (Message r))
deliver p = case fPop (pToSelf p) of
    Just (m, inbox) -> (internalDeliver m p{pToSelf=inbox}, Just m)
    Nothing -> case dqDequeue (pVC p) (pDQ p) of
        Just (dq, m) -> (internalDeliver m p{pDQ=dq}, Just m)
        Nothing -> (p, Nothing)

-- | Remove and return all sent messages so the application can broadcast them
-- (in sent-order, eg, with 'foldl'' or 'mapM_').
--
-- >>> send "hello" $ pNew 0 2
-- Process {pID = 0, pVC = VC [1,0], pDQ = DelayQueue [], pToSelf = FIFO [...], pToNetwork = FIFO [...]}
--
-- >>> let (p, ms) = drainBroadcasts . send "hello" $ pNew 0 2
-- >>> p
-- Process {pID = 0, pVC = VC [1,0], pDQ = DelayQueue [], pToSelf = FIFO [...], pToNetwork = FIFO []}
-- >>> ms
-- [Message {mSender = 0, mSent = VC [1,0], mRaw = "hello"}]
--
{-@ reflect drainBroadcasts @-}
drainBroadcasts :: Process r -> (Process r, [Message r])
drainBroadcasts p =
    ( p{pToNetwork=fNew}
    , fList (pToNetwork p)
    )
