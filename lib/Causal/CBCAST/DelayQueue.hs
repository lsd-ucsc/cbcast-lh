module Causal.CBCAST.DelayQueue where

import Redefined

import Causal.VectorClock
import Causal.CBCAST.Message


-- * Types

type DQList r = [Message r]
{-@ type DQListS r S = [{m:Message r | listLength (mSent m) == S}] @-}

-- TODO: sortedness invariant
-- FIXME (NEWTYPE_RESTRICTION)
data DelayQueue r = DelayQueue
    { dqPCount :: Int
    , dqList :: DQList r
    }
{-@
data DelayQueue [dqSize] r = DelayQueue
    { dqPCount :: Nat
    , dqList :: DQListS r dqPCount
    }
@-}


-- * Logical predicates

{-@ measure dqSize @-}
{-@ dqSize :: _ -> Nat @-}
dqSize :: DelayQueue r -> Int
dqSize (DelayQueue _ xs) = listLength xs


-- * User API

-- | Make a new empty delay-queue.
{-@ dqNew :: Nat -> DelayQueue r @-}
dqNew :: Int -> DelayQueue r
dqNew pCount = DelayQueue pCount []
{-@ inline dqNew @-}

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
{-@ inline dqEnqueue @-}
{-@
dqEnqueue
    :: m:Message r
    -> {xs:DelayQueue r | listLength (mSent m) == dqPCount xs}
    -> {ys:DelayQueue r | dqSize xs + 1 == dqSize ys && dqPCount xs == dqPCount ys}
@-}
dqEnqueue :: Message r -> DelayQueue r -> DelayQueue r
dqEnqueue m (DelayQueue pCount xs) = DelayQueue pCount (dqEnqueueImpl pCount m xs)

{-@ reflect dqEnqueueImpl @-}
{-@
dqEnqueueImpl
    :: pCount:Nat
    -> {m:Message r | listLength (mSent m) == pCount}
    -> xs:DQListS r pCount
    -> {ys:DQListS r pCount | listLength xs + 1 == listLength ys}
@-}
dqEnqueueImpl :: Int -> Message r -> [Message r] -> [Message r]
dqEnqueueImpl _ m [] = [m]
dqEnqueueImpl pCount m (x:xs)
    | mSent x `vcLessEqual` mSent m = x : dqEnqueueImpl pCount m xs
    | otherwise = m : x:xs

-- | Pop the first deliverable message from the delay-queue, if any.
{-@ inline dqDequeue @-}
{-@
dqDequeue
    :: p:Proc
    -> {xs:DelayQueue r | listLength (pTime p) == dqPCount xs}
    -> Maybe
        ( {ys:DelayQueue r | dqSize xs == 1 + dqSize ys && dqPCount xs == dqPCount ys}
        , {m:Message r | deliverable p m}
        )
@-}
dqDequeue :: Proc -> DelayQueue r -> Maybe (DelayQueue r, Message r)
dqDequeue p (DelayQueue pCount xs) = case dqDequeueImpl pCount p xs of
    Nothing -> Nothing
    Just (ys, y) -> Just (DelayQueue pCount ys, y)

{-@ reflect dqDequeueImpl @-}
{-@
dqDequeueImpl
    :: pCount:Nat
    -> {p:Proc | listLength (pTime p) == pCount}
    -> xs:DQListS r pCount
    -> Maybe
        ( {ys:DQListS r pCount | listLength xs == 1 + listLength ys}
        , {m:Message r | deliverable p m}
        )
@-}
dqDequeueImpl :: Int -> Proc -> [Message r] -> Maybe ([Message r], Message r)
dqDequeueImpl _ _ [] = Nothing
dqDequeueImpl pCount p (x:xs)
    | deliverable p x = Just (xs, x)
    | otherwise = case dqDequeueImpl pCount p xs of
        Nothing -> Nothing
        Just (ys, y) -> Just (x:ys, y)
