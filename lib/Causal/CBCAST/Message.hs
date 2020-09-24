module Causal.CBCAST.Message where

import qualified Data.UUID as U
import Causal.VectorClockConcrete (VectorClock)

type PID = U.UUID
type VT = VectorClock

data Message raw = Message { mSender :: PID, mSent :: VT, mRaw :: raw }
