
-- | Proof shims to make types correct for proving preservation properties.
module UCausalDelivery_Shims where

import Language.Haskell.Liquid.ProofCombinators
import Redefined.Fin
import Redefined.Ord
import Redefined.Proof (proofConst)

import SystemModel
import Properties
import Properties2
import UCausalDelivery

-- | The deliver function, but throw away the message.
{-@ deliverShim :: p:P r -> PasP r {p} @-}
deliverShim :: P r -> P r
deliverShim p =
    case deliver p of
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

-- | The broadcast function, but throw away the message.
{-@ broadcastShim :: r -> p:P r -> PasP r {p} @-}
broadcastShim :: r -> P r -> P r
broadcastShim raw p =
    let (_, p') = broadcast raw p in p'
{-@ inline broadcastShim @-}
