-- | CBCAST message type and definition of deliverability.
--
-- To follow the proof, read VectorClock.hs first, this file, then
-- Safety.hs.
module Causal.CBCAST.Message where

import Redefined
import Causal.CBCAST.VectorClock


-- * Types

-- | Message type used throughout implementation.
{-@
data Message r = Message { mSender::PID, mSent::VC, mRaw::r } @-}
data Message r = Message { mSender::PID, mSent::VC, mRaw::r }

-- | Process metadata used for deliverability, distinct from process state.
{-@
data Proc = Proc { procId :: PID, procVc :: VC } @-}
data Proc = Proc { procId :: PID, procVc :: VC }


-- * Deliverability

-- | page 10/281:
--
--      "(2) On reception of message m sent by p_i and timestamped with VT(m),
--      process p_j =/= p_i delays delivery of m until:
--
--          for-all k: 1...n { VT(m)[k] == VT(p_j)[k] + 1 if k == i
--                           { VT(m)[k] <= VT(p_j)[k]     otherwise"
--
{-@ reflect deliverableK @-}
{-@
deliverableK :: Message r -> Proc -> PID -> Bool @-}
deliverableK :: Message r -> Proc -> PID -> Bool
deliverableK m p k
    | k == mSender m = mSent m ! k == procVc p ! k + 1
    | k /= mSender m = mSent m ! k <= procVc p ! k
    | otherwise = impossibleConst False "all cases covered"

-- | @deliverable m p@ computes whether a message sent by @senderId m@ at @messageVc
-- m@ is deliverable to @procId p@ at @procVc p@.
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
-- >>> let p = Proc 0 $ VC [1,0]
-- >>> deliverable (Message 0 (VC [1,0]) "hello") p
-- False
-- >>> deliverable (Message 1 (VC [1,1]) "world") p
-- True
--
{-@ reflect deliverable @-}
{-@
deliverable :: Message r -> Proc -> Bool @-}
deliverable :: Message r -> Proc -> Bool
deliverable m p = deliverableK m p `andAtEachK` vcSize (mSent m)
