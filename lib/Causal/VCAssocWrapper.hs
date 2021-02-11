-- | Wrapper around "VCAssoc" with PIDs anchored to UUID. LH has trouble
-- reflecting functions that have UUID in the type, but if we hide it inside a
-- data constructor in this module, it works.
module Causal.VCAssocWrapper
( module Causal.VCAssocWrapper
, module Causal.VCAssoc
) where

import Data.UUID (UUID)
import Causal.VCAssoc

type PID = UUID
{-@
data VC = VC (VCAssoc PID) @-}
data VC = VC (VCAssoc PID)
    deriving Eq

{-@ inline vcPidsMatch @-}
vcPidsMatch :: VC -> VC -> Bool
vcPidsMatch (VC a) (VC b) = vcaPidsMatch a b

vcNew :: VC
vcNew = VC vcaNew
{-@ inline vcNew @-}

vcTick :: UUID -> VC -> VC
vcTick pid (VC x) = VC (vcaTick pid x)
{-@ inline vcTick @-}

{-@ vcRead :: UUID -> VC -> Clock @-}
vcRead :: UUID -> VC -> Clock
vcRead pid (VC x) = vcaRead pid x
{-@ inline vcRead @-}

vcCombine :: VC -> VC -> VC
vcCombine (VC a) (VC b) = VC (vcaCombine a b)
{-@ inline vcCombine @-}

vcLessEqual :: VC -> VC -> Bool
vcLessEqual (VC a) (VC b) = vcaLessEqual a b
{-@ inline vcLessEqual @-}

vcLess :: VC -> VC -> Bool
vcLess (VC a) (VC b) = vcaLess a b
{-@ inline vcLess @-}

-- | @vcDeliverable mSender mSent localTime@ computes whether a message sent by
-- @mSender@ at @mSent@ is deliverable at @localTime@.
{-@ inline vcDeliverable @-}
{-@ vcDeliverable :: PID -> m:VC -> {p:VC | vcPidsMatch m p} -> Bool @-}
vcDeliverable :: PID -> VC -> VC -> Bool
vcDeliverable mSender (VC mSent) (VC localTime) = vcaDeliverable mSender mSent localTime
