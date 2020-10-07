module Causal.CBCAST.Message where

import Data.UUID (UUID)
import Causal.VectorClockConcrete (VectorClock)

type PID = UUID
type VT = VectorClock

data Message raw = Message { mSender :: PID, mSent :: VT, mRaw :: raw }
