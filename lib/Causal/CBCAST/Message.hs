-- | CBCAST message type and definition of deliverability.
--
-- To follow the proof, read VectorClock.hs first, this file, then
-- Safety.hs.
module Causal.CBCAST.Message where

import Causal.CBCAST.VectorClock


-- * Types

-- | Message type used throughout implementation.
{-@
data Message r = Message { mSender::PID, mSent::VC, mRaw::r } @-}
data Message r = Message { mSender::PID, mSent::VC, mRaw::r }
    deriving (Eq, Show)


-- * Deliverability

-- | page 10/281:
--
--      "(2) On reception of message m sent by p_i and timestamped with VT(m),
--      process p_j =/= p_i delays delivery of m until:
--
--          for-all k: 1...n { VT(m)[k] == VT(p_j)[k] + 1 if k == i
--                           { VT(m)[k] <= VT(p_j)[k]     otherwise"
--
-- @deliverableK m procVc k@ computes whether the @k@th offsets into the
-- message send-time @mSent m@ and the local-time @procVc@ allow for the
-- message to be delivered. Delivery is only allowed when @deliverableK m
-- procVc@ is true for all @k@.
{-@ reflect deliverableK @-}
{-@
deliverableK :: Message r -> VC -> PID -> Bool @-}
deliverableK :: Message r -> VC -> PID -> Bool
deliverableK m procVc k
    | k == mSender m = mSent m ! k == (procVc ! k) + 1
    | otherwise      = mSent m ! k <= procVc ! k

-- | @deliverable m p@ computes whether a message sent by @mSender m@ at @mSent
-- m@ is deliverable at local-time @procVc@.
--
--
-- Example:
--
-- P0 and P1 both start at [0,0].
-- >    P0@[0,0]    P1@[0,0]
--
-- P0 sends "hello" causing it to increment its own vector clock and append
-- that to the message.
-- >    P0@[1,0]    P1@[0,0]
--
-- P1 receives the message from P0, delivers it, and applies the attached
-- vector clock.
-- >    P0@[1,0]    P1@[1,0]
--
-- P1 sends "world" causing it to increment its own vector clock and append
-- that to the message.
-- >    P0@[1,0]    P1@[1,1]
--
-- What does P0 think of the deliverability of both messages?
--
--      * The "hello"@[1,0] is not deliverable at P0.
--      * The "world"@[1,1] is deliverable at P0.
--
-- From this we conclude that "Process p_j need not delay messages received
-- from itself" means that it actually _cannot_ delay such messages, since they
-- won't be considered deliverable. This interpretation is bolstered by the
-- precondition in (2) "On reception of message m sent by p_i, process p_j =/=
-- p_i delays delivery".
--
-- >>> let procVc = VC [1,0]
-- >>> deliverable (Message 0 (VC [1,0]) "hello") procVc
-- False
-- >>> deliverable (Message 1 (VC [1,1]) "world") procVc
-- True
--
{-@ reflect deliverable @-}
{-@
deliverable :: Message r -> VC -> Bool @-}
deliverable :: Message r -> VC -> Bool
deliverable m procVc = deliverableK m procVc `andAtEachK` vcSize (mSent m)
