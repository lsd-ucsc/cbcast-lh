-- | Wrapper around "VCAssoc" with PIDs anchored to UUID. LH has trouble
-- reflecting functions that have UUID in the type, but if we hide it inside a
-- data constructor in this module, it works.
module Causal.VectorClock
( PID
, VC(..)
, vcNew
, vcTick
, vcRead
, vcLessEqual
, vcLess
, VCAssoc(..)
) where

import Data.UUID (UUID)
import Causal.VCAssoc

type PID = UUID
{-@
data VC = VC (VCAssoc PID) @-}
data VC = VC (VCAssoc PID)
    deriving Eq

vcNew :: VC
vcNew = VC vcaNew
{-@ inline vcNew @-}

vcTick :: UUID -> VC -> VC
vcTick pid (VC x) = VC (vcaTick pid x)
{-@ inline vcTick @-}

vcRead :: UUID -> VC -> Clock
vcRead pid (VC x) = vcaRead pid x
{-@ inline vcRead @-}

vcLessEqual :: VC -> VC -> Bool
vcLessEqual (VC a) (VC b) = vcaLessEqual a b
{-@ inline vcLessEqual @-}

vcLess :: VC -> VC -> Bool
vcLess (VC a) (VC b) = vcaLess a b
{-@ inline vcLess @-}
