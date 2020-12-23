module Causal.CBCAST.Message where

import Data.UUID (UUID)
import Causal.VectorClockSledge

type PID = UUID
type VT = VectorClock

{-@
data Message raw = Message { mSender :: PID, mSent :: VT, mRaw :: raw } @-}
data Message raw = Message { mSender :: PID, mSent :: VT, mRaw :: raw }
