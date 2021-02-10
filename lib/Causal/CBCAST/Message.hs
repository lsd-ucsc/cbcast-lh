{-# LANGUAGE NamedFieldPuns #-}
module Causal.CBCAST.Message where

import Redefined

import Causal.VectorClock

{-@
data Message raw = Message { mSender :: PID, mSent :: VC, mRaw :: raw } @-}
data Message raw = Message { mSender :: PID, mSent :: VC, mRaw :: raw }
    deriving Eq


-- * Deliverability

-- | Determine message deliverability relative to current vector time.
--
--      "(2) On reception of message m sent by p_i and timestamped with VT(m),
--      process p_j =/= p_i delays delivery of m until:
--
--          for-all k: 1...n { VT(m)[k] == VT(p_j)[k] + 1 if k == i
--                           { VT(m)[k] <= VT(p_j)[k]     otherwise"
{-@ inline deliverable @-}
{-@ deliverable :: m:Message r -> {p:VC | vcPidsMatch (mSent m) p} -> Bool @-}
deliverable :: Message r -> VC -> Bool
deliverable Message{mSender, mSent} localTime = vcDeliverable mSender mSent localTime

-- | TODO decide whether this belongs in the VectorClock module or can be folded into the above
{-@ inline vcDeliverable @-}
{-@ vcDeliverable :: PID -> m:VC -> {p:VC | vcPidsMatch m p} -> Bool @-}
vcDeliverable :: PID -> VC -> VC -> Bool
vcDeliverable mSender (VC mSent) (VC localTime) = vcaDeliverable mSender mSent localTime

-- | TODO decide whether this belongs in the VCAssoc module
{-@ reflect vcaDeliverable @-}
{-@ ple vcaDeliverable @-}
{-@ vcaDeliverable :: pid -> m:VCAssoc pid -> {p:VCAssoc pid | vcaPidsMatch m p} -> Bool @-}
vcaDeliverable :: Ord pid => pid -> VCAssoc pid -> VCAssoc pid -> Bool
vcaDeliverable _ Nil Nil = True
vcaDeliverable _ Nil VCA{} = impossibleConst False "VCs have the same set of PIDs"
vcaDeliverable _ VCA{} Nil = impossibleConst False "VCs have the same set of PIDs"
vcaDeliverable mSender (VCA mIdx mClock mRest) (VCA pIdx pClock pRest)
    | mIdx == pIdx && mIdx == mSender   = mClock == pClock + 1 && vcaDeliverable mSender mRest pRest
    | mIdx == pIdx && mIdx /= mSender   = mClock <= pClock     && vcaDeliverable mSender mRest pRest
    | otherwise                         = impossibleConst False "VCs have the same set of PIDs"


-- * Old deliverability

-- | Old notion of deliverability
data Deliverability = Early | Ready | Late deriving (Eq, Show)

-- | Old notion of deliverability which doesn't need a `vcRead` but is hard to
-- mentally map to the paper's definition.
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
