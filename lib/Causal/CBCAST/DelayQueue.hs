module Causal.CBCAST.DelayQueue
{-( DelayQueue()
, dqNew
, dqEnqueue
, dqDequeue
, dqSize
)-} where

import Redefined

import Causal.CBCAST.Message
import Causal.VectorClockSledge


-- * Types

data Deliverability = Early | Ready | Late deriving (Eq, Show)

-- {-@ data DelayQueue [dqSize] @-}
data DelayQueue r = DelayQueue [Message r] -- FIXME: this is supposed to be a newtype, but that breaks the LH measure


-- * Logical predicates

{-@
dqSize :: _ -> Nat @-}
dqSize :: DelayQueue r -> Int
dqSize (DelayQueue xs) = listLength xs
{-@ measure dqSize @-}

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
{-@ reflect deliverability @-}


-- * User API

-- | Make a new empty delay-queue.
dqNew :: DelayQueue r
dqNew = DelayQueue []
{-@ inline dqNew @-}

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
{-@ inline dqEnqueue @-}

dqEnqueueImpl :: Message r -> [Message r] -> [Message r]
dqEnqueueImpl m [] = [m]
dqEnqueueImpl m (x:xs)
    | mSent x `vcLessEqual` mSent m = x : dqEnqueueImpl m xs
    | otherwise = m : x:xs
{-@ reflect dqEnqueueImpl @-}

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
{-@ dqDequeue :: _ -> a:_ -> Maybe ({b:_ | dqSize a - 1 == dqSize b}, _) @-}
dqDequeue :: VT -> DelayQueue r -> Maybe (DelayQueue r, Message r)
dqDequeue t (DelayQueue xs)
    = maybeMap (\(dq, m) -> (DelayQueue dq, m))
    $ extractFirstBy (\m -> deliverability t m == Ready) xs
{-@ reflect dqDequeue @-}

{-@ extractFirstBy :: _ -> xs:_ -> Maybe ({ys:_ | listLength xs - 1 == listLength ys}, _) @-}
extractFirstBy :: (a -> Bool) -> [a] -> Maybe ([a], a)
extractFirstBy predicate xs = case listBreak predicate xs of
    (before, x:after) -> Just (before `listAppend` after, x)
    _ -> Nothing
{-@ inline extractFirstBy @-}
