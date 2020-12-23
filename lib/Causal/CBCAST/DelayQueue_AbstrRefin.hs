module Causal.CBCAST.DelayQueue_AbstrRefin where

import Redefined

import Causal.CBCAST.Message
import Causal.VectorClockSledge


-- * Types

-- | Alias defining the sort order of a valid delay-queue list.
--
-- NOTE: In LH, type alias refinements are only carried on functions which
-- specify the type alias in a refinement type. For that reason, no
-- corresponding haskell type alias is defined here (its use would be
-- misleading).
{-@
type DQList = [Message r]<{\a b -> dqlMessagesAreSorted a b}> @-}

{-@
data DelayQueue [dqSize] r = DelayQueue DQList      @-}
data DelayQueue          r = DelayQueue [Message r]

data Deliverability = Early | Ready | Late deriving (Eq, Show)


-- * Logical predicates

{-@
dqSize :: _ -> Nat @-}
dqSize :: DelayQueue r -> Int
dqSize (DelayQueue xs) = listLength xs
{-@ measure dqSize @-}

-- | Predicate: Are the messages sorted as a delay-queue list specifies?
dqlMessagesAreSorted :: Message r -> Message r -> Bool
dqlMessagesAreSorted a b = vcLessEqual (mSent a) (mSent b)
{-@ inline dqlMessagesAreSorted @-}

-- | Predicate: Is the message sorted before the delay-queue list?
{-@
dqlMessageIsBefore :: Message r -> DQList -> Bool @-}
dqlMessageIsBefore :: Message r -> [Message r] -> Bool
dqlMessageIsBefore _ [] = True
dqlMessageIsBefore m (x:_) = dqlMessagesAreSorted m x
{-@ inline dqlMessageIsBefore @-}


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
---- dqEnqueue :: Message r -> DelayQueue r -> DelayQueue r
---- dqEnqueue m (DelayQueue xs) = DelayQueue (dqEnqueueImpl m xs)

-- {-@
-- dqEnqueueImpl :: Message r -> DQList -> DQList @-}
dqEnqueueImpl :: Message r -> [Message r] -> [Message r]
dqEnqueueImpl m [] = [m]
dqEnqueueImpl m (x:xs)
    | mSent x `vcLessEqual` mSent m = x : dqEnqueueImpl m xs
    | otherwise = m : x:xs


---- -- | Determine message deliverability relative to current vector time.
---- --
---- --      "(2) On reception of message m sent by p_i and timestamped with VT(m),
---- --      process p_j =/= p_i delays delivery of m until:
---- --
---- --          for-all k: 1...n { VT(m)[k] == VT(p_j)[k] + 1 if k == i
---- --                           { VT(m)[k] <= VT(p_j)[k]     otherwise"
---- deliverability :: VT -> Message r -> Deliverability
---- deliverability t m
----     -- The value at every index is LE than in t. Message should have already
----     -- been delivered.
----     | mSent m `vcLessEqual` t = Late
----     -- The value at one or more indexes is GT in t. If we increment only the
----     -- sender index and find true, then only that one was GT in t and it was
----     -- exactly (+1) the value in t.
----     | mSent m `vcLessEqual` vcTick (mSender m) t = Ready
----     -- The value at more than one index is GT in t.
----     | otherwise = Early
----
---- -- | Extract a message from the queue if one is deliverable according to the
---- -- vector time. The new queue is returned with the first deliverable message.
---- --
---- --      "(2) On reception of message m sent by p_i and timestamped with VT(m),
---- --      process p_j =/= p_i delays delivery of m until:
---- --
---- --          for-all k: 1...n { VT(m)[k] == VT(p_j)[k] + 1 if k == i
---- --                           { VT(m)[k] <= VT(p_j)[k]     otherwise"
---- --
---- -- Abstracting the VC implementation means we cannot actually check this
---- -- exactly as written. See 'deliverability' to see how it's checked.
---- dqDequeue :: VT -> DelayQueue r -> Maybe (DelayQueue r, Message r)
---- dqDequeue t (DelayQueue xs)
----     = fmapMaybe (first DelayQueue)
----     $ extractFirstBy (\m -> deliverability t m == Ready) xs
----
---- extractFirstBy :: (a -> Bool) -> [a] -> Maybe ([a], a)
---- extractFirstBy predicate xs = case break predicate xs of
----     (before, x:after) -> Just (before ++ after, x)
----     _ -> Nothing
----
---- -- * Verification
----
----
---- {-@ data DelayQueue [dqSize] @-}
----
---- {-@ dqDequeue :: _ -> a:_ -> Maybe ({b:_ | dqSize a - 1 == dqSize b}, _) @-}
---- {-@ extractFirstBy :: _ -> xs:_ -> Maybe ({ys:_ | listLength xs - 1 == listLength ys}, _) @-}
