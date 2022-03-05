
-- | Types and functions to use vector clocks in a message passing algorithm.
module MessagePassingAlgorithm.VectorClockAdapter where

import VectorClock
import MessagePassingAlgorithm




-- * Datatypes

-- | Message metadata for an MPA that uses VCs.
{-@
data VCMM = VCMM {vcmmSent::VC, vcmmSender::PIDasV {vcmmSent}} @-}
data VCMM = VCMM {vcmmSent::VC, vcmmSender::PID}
    deriving Eq
{-@ type VCMMsized N = {mm:VCMM | len (vcmmSent mm) == N} @-}
{-@ type VCMMasM M = VCMMsized {len (mVC M)} @-}

-- | Message in an MPA that uses VCs.
{-@
type M r = Message VCMM r @-} -- QQQ: Why is this required?
type M r = Message VCMM r
{-@ type Msized r N = {m:M r | len (mVC m) == N} @-}
{-@ type MasM r M = Msized r {len (mVC M)} @-}
{-@ type MasV r V = Msized r {len V} @-}

-- | Vector clock sized to a message that uses VCs.
{-@ type VCasM M = VCsized {len (mVC M)} @-}

-- | ProcessHistory in an MPA that uses VCs.
type H r = ProcessHistory VCMM r
{-@ type Hsized r N = ProcessHistory (VCMMsized {N}) r @-}




-- * Field accessors

-- | Message vector clock
{-@
mVC :: Message VCMM r -> VC @-}
mVC :: Message VCMM r -> VC
mVC m = vcmmSent (mMetadata m)
{-@ inline mVC @-}
-- QQQ: When defined with pattern matching, broke several proofs.
-- TODO: re-type these two functions to use M r

-- | Message sender PID
{-@
mSender :: m:Message VCMM r -> PIDsized {len (mVC m)} @-}
mSender :: Message VCMM r -> PID
mSender m = vcmmSender (mMetadata m)
{-@ inline mSender @-}
-- QQQ: When defined with pattern matching, broke several proofs.



-- * Convenience relations

-- | Message order convenience operator @a ===> b@ is true when the vector
-- clock in @a@ is less than that of @b@.
{-@
(===>) :: m:M r -> MasM r {m} -> Bool @-}
(===>) :: M r -> M r -> Bool
a ===> b = mVC a `vcLess` mVC b
{-@ reflect ===> @-}

-- | Message order convenience operator @a |||| b@ is true when the vector
-- clock in @a@ is concurrent with that of @b@.
{-@
(||||) :: m:M r -> MasM r {m} -> Bool @-}
(||||) :: M r -> M r -> Bool
a |||| b = mVC a `vcConcurrent` mVC b
{-@ reflect |||| @-}




-- * Other operations

-- | When putting events into process history it's necessary to specify the vc
-- size in the type of the metadata.
{-@
coerce :: m:Message VCMM r -> {m':Message (VCMMasM {m}) r | m == m'} @-}
coerce :: Message VCMM r -> Message VCMM r
coerce (Message a b) = Message a b
{-@ reflect coerce @-}
