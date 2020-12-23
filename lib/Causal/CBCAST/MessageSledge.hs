module Causal.CBCAST.MessageSledge where

import Data.UUID (UUID)
import Causal.VectorClockSledge ()

type PID = UUID

{-@
data Message vt raw = Message { mSender :: PID, mSent :: vt, mRaw :: raw } @-}
data Message vt raw = Message { mSender :: PID, mSent :: vt, mRaw :: raw }

