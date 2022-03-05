
-- | Local process data and properties in a message passing algorithm.
module MessagePassingAlgorithm where

import Redefined

-- | Process identifier
{-@
type PID = Nat @-}
type PID = Fin
{-@ type PIDsized N = Fin {N} @-}

-- | Message envelope, containing metadata (parameterized by a message passing
-- algorithm) and raw content (parameterized by a user application).
{-@
data Message mm r = Message {mMetadata::mm, mRaw::r} @-}
data Message mm r = Message {mMetadata::mm, mRaw::r}
    deriving Eq

-- | Record of the act of broadcasting a message or delivering (to the user
-- local user application for processing) a message.
data Event mm r
    = Broadcast (Message mm r)
    | Deliver PID (Message mm r)
    deriving Eq -- oops

-- | History of events. Events are added to the left using cons (:). If events
-- 1, 2, and 3 occur, history will be 3:2:1:[].
type ProcessHistory mm r = [Event mm r]
