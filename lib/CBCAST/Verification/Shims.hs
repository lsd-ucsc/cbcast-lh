{-# OPTIONS_GHC "-Wno-unused-imports" #-} -- LH needs bodies of reflected definitions
{-# OPTIONS_GHC "-Wno-warnings-deprecations" #-} -- Hide the "verification only" and "internal use" warnings

-- | Functions /inlined/ to LH that extract the process after transitions.
-- These make writing proofs about how the process is affected by a transition
-- easier to write.
module CBCAST.Verification.Shims {-# WARNING "Verification only" #-} where

import VectorClock
import CBCAST.Core
import CBCAST.Transitions
import CBCAST.Step

-- | The first two steps of broadcast (prepare and inject message) without the
-- third step (deliver).
{-@ broadcastPrepareInjectShim :: r -> p:Process r -> PasP r {p} @-}
broadcastPrepareInjectShim :: r -> Process r -> Process r
broadcastPrepareInjectShim raw p =
    broadcastHelper_inject (broadcastHelper_prepare raw p) p
{-@ inline broadcastPrepareInjectShim @-}

-- | The internalBroadcast function, but throw away the message.
{-@ broadcastShim :: r -> p:Process r -> PasP r {p} @-}
broadcastShim :: r -> Process r -> Process r
broadcastShim raw p =
    let (_, p') = internalBroadcast raw p in p'
{-@ inline broadcastShim @-}

-- | The internalDeliver function, but throw away the message.
{-@ deliverShim :: p:Process r -> PasP r {p} @-}
deliverShim :: Process r -> Process r
deliverShim p =
    case internalDeliver p of
        Nothing -> p
        Just (_, p') -> p'
{-@ inline deliverShim @-}

-- | The step function but only keeps the process.
{-@ stepShim :: op:Op r -> PasOP r {op} -> PasOP r {op} @-}
stepShim :: Op r -> Process r -> Process r
stepShim op p₀ = case step op p₀ of
    ResultReceive _ p             -> p
    ResultBroadcast _ (_, p)      -> p
    ResultDeliver _ (Just (_, p)) -> p
    ResultDeliver _ Nothing       -> p₀
{-@ inline stepShim @-}
