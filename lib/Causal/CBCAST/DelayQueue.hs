{-# LANGUAGE NamedFieldPuns #-}
module Causal.CBCAST.DelayQueue where

import Redefined.List

import Causal.CBCAST.VectorClock
import Causal.CBCAST.Message


-- * Types

-- | A delay queue excludes the messages from the current process.
{-@
data DelayQueue [dqSize] r = DelayQueue
    { dqSelf :: PID
    , dqList :: [{m:Message r | mSender m /= dqSelf}]
    }
@-}
data DelayQueue r = DelayQueue
    { dqSelf :: PID
    , dqList :: [Message r]
    }
    deriving (Eq, Show)

{-@
type DQ r PID = {dq:DelayQueue r | dqSelf dq == PID} @-}
type DQ r = DelayQueue r


-- * Logical predicates

{-@ measure dqSize @-}
{-@ dqSize :: DelayQueue r -> Nat @-}
dqSize :: DelayQueue r -> Int
dqSize DelayQueue{dqList} = listLength dqList


-- * User API

-- | Make a new empty delay-queue.
{-@ reflect dqNew @-}
{-@ dqNew :: p:PID -> DQ r {p} @-}
dqNew :: PID -> DelayQueue r
dqNew dqSelf = DelayQueue{dqSelf, dqList=[]}

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
    :: m:Message r
    -> {xs:DelayQueue r | mSender m /= dqSelf xs}
    -> {ys:DelayQueue r | dqSize xs + 1 == dqSize ys && dqSelf xs == dqSelf ys}
@-}
dqEnqueue :: Message r -> DelayQueue r -> DelayQueue r
dqEnqueue m dq = dq{dqList=insertAfterBy mSentLessEqual m (dqList dq)}

{-@ reflect mSentLessEqual @-}
mSentLessEqual :: Message r -> Message r -> Bool
mSentLessEqual m1 m2 = mSent m1 `vcLessEqual` mSent m2

-- | Pop the first deliverable message from the delay-queue, if any.
{-@ reflect dqDequeue @-}
{-@
dqDequeue
    :: procVc:VC
    -> xs:DelayQueue r
    -> Maybe
        ( {ys:DelayQueue r | dqSize xs - 1 == dqSize ys && dqSelf xs == dqSelf ys}
        , {m:Message r | deliverable m procVc}
        )
@-}
dqDequeue :: VC -> DelayQueue r -> Maybe (DelayQueue r, Message r)
dqDequeue _ DelayQueue{dqList=[]} = Nothing
dqDequeue procVc dq@DelayQueue{dqList=x:xs}
    | deliverable x procVc = Just (dq{dqList=xs}, x)
    | otherwise = case dqDequeue procVc dq{dqList=xs} of
        Just (DelayQueue{dqList=ys}, y) -> Just (dq{dqList=x:ys}, y)
        Nothing -> Nothing

-- * Implementation

-- TODO: sort by invariant
-- {-@ type TODO a LT = [a]<\x -> { _:({y:a | LT x y}) | true }> @-}
-- {-@ type TODO a LT = [a]<\x y -> LT x y> @-}

-- | @insertAfterBy lt a xs@ inserts @a@ into @xs@ /after/ the values from @xs@
-- for which @`lt` a@ is satisfied.
--
-- >>> insertAfterBy (\(a, _) (b, _) -> a <= b) ('b',-10) [('a',0),('b',1),('c',2)]
-- [('a',0),('b',1),('b',-10),('c',2)]
--
-- As distinct from 'insert' and 'insertBy', which insert into the first position:
--
-- >>> import Data.List
-- >>> insert ('b',-10) [('a',0),('b',1),('c',2)]
-- [('a',0),('b',-10),('b',1),('c',2)]
-- >>> insertBy (\(a, _) (b, _) -> compare a b) ('b',-10) [('a',0),('b',1),('c',2)]
-- [('a',0),('b',-10),('b',1),('c',2)]
--
-- We can simulate that too by comparing more strictly:
--
-- >>> insertAfterBy (\(a, _) (b, _) -> a < b) ('b',-10) [('a',0),('b',1),('c',2)]
-- [('a',0),('b',-10),('b',1),('c',2)]
--
{-@ reflect insertAfterBy @-}
{-@
insertAfterBy
    :: lt:(a -> a -> Bool)
    -> a
    -> xs:[a]
    -> {ys:[a] | listLength xs + 1 == listLength ys}
@-}
insertAfterBy :: (a -> a -> Bool) -> a -> [a] -> [a]
insertAfterBy _ a [] = [a]
insertAfterBy lt a (x:xs)
    | x `lt` a = x : insertAfterBy lt a xs
    | otherwise = a : x:xs

-- | @popFirstBy ready xs@ removes and returns the first element of @xs@ which
-- satisfies the predicate @ready@, as well as the modified list.
--
-- >>> popFirstBy (> 2) [0..5]
-- Just ([0,1,2,4,5],3)
--
-- >>> popFirstBy (> 20) [0..5]
-- Nothing
--
{-@ reflect popFirstBy @-}
{-@
popFirstBy
    :: ready:(a -> Bool)
    -> xs:[a]
    -> Maybe
        ( {ys:[a] | listLength xs - 1 == listLength ys}
        , {x:a | ready x}
        )
@-}
popFirstBy :: (a -> Bool) -> [a] -> Maybe ([a], a)
popFirstBy _ [] = Nothing
popFirstBy ready (x:xs)
    | ready x = Just (xs, x)
    | otherwise = case popFirstBy ready xs of
        Just (ys, y) -> Just (x:ys, y)
        Nothing -> Nothing
