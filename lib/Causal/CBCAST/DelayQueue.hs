module Causal.CBCAST.DelayQueue
( DelayQueue()
, dqNew
, dqEnqueue
, dqDequeue
, dqSize
) where

import Control.Arrow (first)
import Verification (listLength)

import Causal.CBCAST.Message
import Causal.VectorClockConcrete

data Deliverability = Early | Ready | Late deriving (Eq, Show)

data DelayQueue r = DelayQueue [Message r] -- FIXME: this is supposed to be a newtype, but that breaks the LH measure

-- | Determine message deliverability relative to current vector time.
--
--      "(2) On reception of message m sent by p_i and timestamped with VT(m),
--      process p_j =/= p_i delays delivery of m until:
--
--          for-all k: 1...n { VT(m)[k] == VT(p_j)[k] + 1 if k == i
--                           { VT(m)[k] <= VT(p_j)[k]     otherwise"
deliverability :: VT -> Message r -> Deliverability
deliverability t m
    -- The value at every index is LE than in t. Message should have already
    -- been delivered.
    | mSent m `vcLessEqual` t = Late
    -- The value at one or more indexes is GT in t. If we increment only the
    -- sender index and find true, then only that one was GT in t and it was
    -- exactly (+1) the value in t.
    | mSent m `vcLessEqual` vcTick (mSender m) t = Ready
    -- The value at more than one index is GT in t.
    | otherwise = Early

-- | Make a new empty delay-queue.
dqNew :: DelayQueue r
dqNew = DelayQueue []

-- | Insert a message into the delay queue.
--
--      "This queue is sorted by vector time, with concurrent messages ordered
--      by time of receipt (however, the queue order will not be used until
--      later in the paper)."
--
-- This is interpreted to mean that a message is inserted past all the messages
-- which are vcLessEqual than it, and messages are extracted from the left
-- first. This achieves FIFO for concurrent messages, and vector time ordering
-- for others.
dqEnqueue :: Message r -> DelayQueue r -> DelayQueue r
dqEnqueue m (DelayQueue xs) = DelayQueue (dqEnqueueImpl m xs)

dqEnqueueImpl :: Message r -> [Message r] -> [Message r]
dqEnqueueImpl m [] = [m]
dqEnqueueImpl m (x:xs)
    | mSent x `vcLessEqual` mSent m = x : dqEnqueueImpl m xs
    | otherwise = m : x:xs

-- | Extract a message from the queue if one is deliverable according to the
-- vector time. The new queue is returned with the first deliverable message.
--
--      "(2) On reception of message m sent by p_i and timestamped with VT(m),
--      process p_j =/= p_i delays delivery of m until:
--
--          for-all k: 1...n { VT(m)[k] == VT(p_j)[k] + 1 if k == i
--                           { VT(m)[k] <= VT(p_j)[k]     otherwise"
--
-- Abstracting the VC implementation means we cannot actually check this
-- exactly as written. See 'deliverability' to see how it's checked.
dqDequeue :: VT -> DelayQueue r -> Maybe (DelayQueue r, Message r)
dqDequeue t (DelayQueue xs) = fmap (first DelayQueue) (dqDequeueImpl t xs)

dqDequeueImpl :: VT -> [Message r] -> Maybe ([Message r], Message r)
dqDequeueImpl t xs = extractFirstBy (\m -> deliverability t m == Ready) xs

extractFirstBy :: (a -> Bool) -> [a] -> Maybe ([a], a)
extractFirstBy predicate xs = case break predicate xs of
    (before, x:after) -> Just (before ++ after, x)
    _ -> Nothing

-- * Verification

{-@ data DelayQueue [dqSize] @-}
{-@ measure dqSize @-}
{-@
dqSize :: DelayQueue r -> Nat @-}
dqSize :: DelayQueue r -> Int
dqSize (DelayQueue xs) = listLength xs
