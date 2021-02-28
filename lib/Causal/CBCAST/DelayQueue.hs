module Causal.CBCAST.DelayQueue where

import Redefined
import Causal.CBCAST.VectorClock
import Causal.CBCAST.Message


-- * Types

{-@
data DelayQueue [dqSize] r = DelayQueue [Message r] @-}
data DelayQueue r = DelayQueue [Message r]
    deriving (Eq, Show)

type DQ r = DelayQueue r
-- TODO: make a generic priority-queue like structure?
--  - List parameterized by content (enables invariants like "messages not sent by me")
--  - List sorted by invariant function (can we define such an alias?)
--  - Enqueue takes the invariant function to perform insert AFTER all True
--  - Dequeue takes a selector function and returns first match


-- * Logical predicates

{-@ measure dqSize @-}
{-@ dqSize :: DelayQueue r -> Nat @-}
dqSize :: DelayQueue r -> Int
dqSize (DelayQueue xs) = listLength xs


-- * User API

-- | Make a new empty delay-queue.
{-@ reflect dqNew @-}
{-@ dqNew :: DelayQueue r @-}
dqNew :: DelayQueue r
dqNew = DelayQueue []

-- | Insert a message into the delay-queue.
--
--      "This queue is sorted by vector time, with concurrent messages ordered
--      by time of receipt (however, the queue order will not be used until
--      later in the paper)."
--
-- This is interpreted to mean that a message is inserted past all the messages
-- which are vcLessEqual than it, and messages are extracted from the left
-- first. This achieves FIFO for concurrent messages, and vector time ordering
-- for others.
--
{-@ reflect dqEnqueue @-}
{-@
dqEnqueue
    :: Message r
    -> xs:DelayQueue r
    -> {ys:DelayQueue r | dqSize xs + 1 == dqSize ys}
@-}
dqEnqueue :: Message r -> DelayQueue r -> DelayQueue r
dqEnqueue m (DelayQueue xs) = DelayQueue (dqEnqueueImpl m xs)

{-@ reflect dqEnqueueImpl @-}
{-@
dqEnqueueImpl
    :: Message r
    -> xs:[Message r]
    -> {ys:[Message r] | listLength xs + 1 == listLength ys}
@-}
dqEnqueueImpl :: Message r -> [Message r] -> [Message r]
dqEnqueueImpl m [] = [m]
dqEnqueueImpl m (x:xs)
    | mSent x `vcLessEqual` mSent m = x : dqEnqueueImpl m xs
    | otherwise = m : x:xs

-- | Pop the first deliverable message from the delay-queue, if any.
{-@ reflect dqDequeue @-}
{-@
dqDequeue
    :: procVc:VC
    -> xs:DelayQueue r
    -> Maybe
        ( {ys:DelayQueue r | dqSize xs - 1 == dqSize ys}
        , {m:Message r | deliverable m procVc}
        )
@-}
dqDequeue :: VC -> DelayQueue r -> Maybe (DelayQueue r, Message r)
dqDequeue procVc (DelayQueue xs) = case dqDequeueImpl procVc xs of
    Nothing -> Nothing
    Just (ys, y) -> Just (DelayQueue ys, y)

{-@ reflect dqDequeueImpl @-}
{-@
dqDequeueImpl
    :: procVc:VC
    -> xs:[Message r]
    -> Maybe
        ( {ys:[Message r] | listLength xs - 1 == listLength ys}
        , {m:Message r | deliverable m procVc}
        )
@-}
dqDequeueImpl :: VC -> [Message r] -> Maybe ([Message r], Message r)
dqDequeueImpl _ [] = Nothing
dqDequeueImpl procVc (x:xs)
    | deliverable x procVc = Just (xs, x)
    | otherwise = case dqDequeueImpl procVc xs of
        Nothing -> Nothing
        Just (ys, y) -> Just (x:ys, y)
