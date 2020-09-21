module Causal.CBCAST.Message where

import qualified Data.UUID as U
import qualified Causal.VectorClockConcrete as VC

type PID = U.UUID
type VT = VC.VectorClock

data Message raw = Message { mSender :: PID, mSent :: VT, mRaw :: raw }
