module Causal.CBCAST.DelayQueue where

import Redefined

import Causal.VectorClock
import Causal.CBCAST.Message


-- * Types

-- FIXME (NEWTYPE_RESTRICTION)
data DelayQueue r = DelayQueue [Message r]
-- TODO: sortedness invariant


-- * Logical predicates

{-@ measure dqSize @-}
{-@ dqSize :: _ -> Nat @-}
dqSize :: DelayQueue r -> Int
dqSize (DelayQueue xs) = listLength xs


-- * User API

-- | Make a new empty delay-queue.
dqNew :: DelayQueue r
dqNew = DelayQueue []
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
--
-- FIXME (REFLECTION_RESTRICTION): We don't use this function, though it's defined with better abstraction than the other version
--
-- TODO: It would be cool to add {m:_ | deliverability t m == Ready} to the result here, as we have with the other definition.
{-
{-@
dqDequeueOriginal :: t:_ -> a:_ -> Maybe ({b:_ | dqSize a - 1 == dqSize b}, _) @-}
dqDequeueOriginal :: VC -> DelayQueue r -> Maybe (DelayQueue r, Message r)
dqDequeueOriginal t (DelayQueue xs)
    = maybeMap (\(dq, m) -> (DelayQueue dq, m))
    $ extractFirstBy (\m -> deliverability t m == Ready) xs
{-@ reflect dqDequeueOriginal @-}

{-@
extractFirstBy :: p:_ -> xs:_ -> Maybe ({ys:_ | listLength xs - 1 == listLength ys}, {y:_ | p y}) @-}
extractFirstBy :: (a -> Bool) -> [a] -> Maybe ([a], a)
extractFirstBy predicate xs = case listBreak predicate xs of
    (before, x:after) -> Just (before `listAppend` after, x)
    _ -> Nothing
{-@ inline extractFirstBy @-}
{-@ ple extractFirstBy @-}
-}


-- ** Alternate dqDequeue

-- FIXME (REFLECTION_RESTRICTION): LH has trouble inlining/reflecting functions
-- that use lambdas and also functions that partially apply other functions. To
-- get around this restriction, we collapse the definitions of dqDequeue,
-- extractFirstBy, listBreak so that the predicate can be expressed without
-- using lambdas or partial applications.

-- | FIXME (REFLECTION_RESTRICTION): This is `extractFirstBy` merged with the
-- original `dqDequeue` to examine the result of `breakOnReady` and extract the
-- first deliverable message to be returned with the delay queue.
--
-- As a result of the merging, we can state directly that the message returned
-- is deliverable.
{-@
dqDequeue :: t:_ -> a:_ -> Maybe ({b:_ | dqSize a - 1 == dqSize b}, {m:_ | deliverability t m == Ready}) @-}
dqDequeue :: VC -> DelayQueue r -> Maybe (DelayQueue r, Message r)
dqDequeue t (DelayQueue xs) =
    case breakOnReady t xs of
        (before, m:after) -> Just (DelayQueue $ before `listAppend` after, m)
        _ -> Nothing
{-@ inline dqDequeue @-}
{-@ ple dqDequeue @-}

-- | FIXME (REFLECTION_RESTRICTION): This is `listBreak` without the predicate
-- argument. The predicate is hardcoded to break on the first deliverable
-- message.
--
-- As a result of the hardcoding, we can state directly that the first list of
-- messages aren't ready, and the head of the second list is.
{-@
breakOnReady :: t:_ -> xs:_ -> ([{m:_ | deliverability t m /= Ready}], {ms:_ | ms /= [] => deliverability t (head ms) == Ready})<{\ys zs -> listLength xs == listLength ys + listLength zs}> @-}
breakOnReady :: VC -> [Message r] -> ([Message r], [Message r])
breakOnReady _ [] = ([], [])
breakOnReady t (m:ms)
    | deliverability t m == Ready = ([], m:ms)
    | otherwise = let (incl,excl) = breakOnReady t ms in (m:incl,excl)
{-@ reflect breakOnReady @-}
