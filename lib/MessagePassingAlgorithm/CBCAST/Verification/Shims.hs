{-# OPTIONS_GHC "-Wno-unused-imports" #-} -- LH needs bodies of reflected definitions

-- | Shim functions to make types correct for proving preservation properties.
module MessagePassingAlgorithm.CBCAST.Verification.Shims where

import VectorClock
import MessagePassingAlgorithm.CBCAST
import MessagePassingAlgorithm.VectorClockAdapter

-- | The internalDeliver function, but throw away the message.
{-@ deliverShim :: p:P r -> PasP r {p} @-}
deliverShim :: P r -> P r
deliverShim p =
    case internalDeliver p of
        Nothing -> p
        Just (_, p') -> p'
{-@ inline deliverShim @-}

-- | The first two steps of broadcast (prepare and inject message) without the
-- third step (deliver).
{-@ broadcastPrepareInjectShim :: r -> p:P r -> PasP r {p} @-}
broadcastPrepareInjectShim :: r -> P r -> P r
broadcastPrepareInjectShim raw p =
    broadcastHelper_injectMessage (broadcastHelper_prepareMessage raw p) p
{-@ inline broadcastPrepareInjectShim @-}

-- | The internalBroadcast function, but throw away the message.
{-@ broadcastShim :: r -> p:P r -> PasP r {p} @-}
broadcastShim :: r -> P r -> P r
broadcastShim raw p =
    let (_, p') = internalBroadcast raw p in p'
{-@ inline broadcastShim @-}
