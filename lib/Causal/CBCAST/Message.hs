{-# LANGUAGE NamedFieldPuns #-}
module Causal.CBCAST.Message where

import Causal.VectorClock

{-@
data Message raw = Message { mSender :: PID, mSent :: VC, mRaw :: raw } @-}
data Message raw = Message { mSender :: PID, mSent :: VC, mRaw :: raw }
    deriving Eq

-- | Determine message deliverability relative to current vector time.
--
--      "(2) On reception of message m sent by p_i and timestamped with VT(m),
--      process p_j =/= p_i delays delivery of m until:
--
--          for-all k: 1...n { VT(m)[k] == VT(p_j)[k] + 1 if k == i
--                           { VT(m)[k] <= VT(p_j)[k]     otherwise"
{-@ inline deliverable @-}
deliverable :: VC -> Message r -> Bool
deliverable t Message{mSender, mSent}
    = vcRead mSender mSent == vcRead mSender (vcTick mSender t)
    && mSent `vcLessEqual` t

data Deliverability = Early | Ready | Late deriving (Eq, Show)

{-@ reflect deliverability @-}
deliverability :: VC -> Message r -> Deliverability
deliverability t m
    -- The value at every index is LE than in t. Message should have already
    -- been delivered.
    | mSent m `vcLessEqual` t = Late
    -- The value at one or more indexes is GT in t. If we increment only the
    -- sender index and find true, then only that one was GT in t and it was
    -- exactly (+1) the value in t.
    | mSent m `vcLessEqual` vcTick (mSender m) t = Ready
    -- The value at more than one index is GT in t.
    | otherwise = Early
