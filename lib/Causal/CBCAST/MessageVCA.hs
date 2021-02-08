{-# LANGUAGE NamedFieldPuns #-}
module Causal.CBCAST.MessageVCA where

import Causal.VCAssoc

{-@
data Message pid raw = Message { mSender :: pid, mSent :: VCAssoc pid, mRaw :: raw } @-}
data Message pid raw = Message { mSender :: pid, mSent :: VCAssoc pid, mRaw :: raw }
    deriving Eq

-- | Determine message deliverability relative to current vector time.
--
--      "(2) On reception of message m sent by p_i and timestamped with VT(m),
--      process p_j =/= p_i delays delivery of m until:
--
--          for-all k: 1...n { VT(m)[k] == VT(p_j)[k] + 1 if k == i
--                           { VT(m)[k] <= VT(p_j)[k]     otherwise"
{-@ inline deliverable @-}
deliverable :: Ord p => VCAssoc p -> Message p r -> Bool
deliverable t Message{mSender, mSent}
    = vcaRead mSender mSent == vcaRead mSender (vcaTick mSender t)
    && mSent `vcaLessEqual` t
