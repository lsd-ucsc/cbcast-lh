{-# OPTIONS_GHC "-Wno-unused-imports" #-} -- LH needs bodies of reflected definitions

-- | Internal CBCAST state-transition functions.
module CBCAST.Transitions where

import Language.Haskell.Liquid.ProofCombinators (Proof, (===), (***), QED(..), (?))
import Language.Haskell.Liquid.ProofCombinatorsExtra (proofConst)

import Redefined
import VectorClock
import CBCAST.Core
import CBCAST.Verification.Core




-- * Transition functions

-- ** Receive

-- | See 'CBCAST.receive'.
{-@
internalReceive :: m:Message r -> PasM r {m} -> PasM r {m} @-}
internalReceive :: Message r -> Process r -> Process r
internalReceive m p
    | mSender m == pID p = p -- NOTE: Ignores network messages with local pid
    | otherwise = p{ pDQ = enqueue m (pDQ p) }
{-@ reflect internalReceive @-}
{-# WARNING internalReceive "Internal use only" #-}




-- ** Deliver

-- | See 'CBCAST.deliver'.
{-@
internalDeliver :: p:Process r -> Maybe (MasP r {p}, PasP r {p}) @-}
internalDeliver :: Process r -> Maybe (Message r, Process r)
internalDeliver p =
    case dequeue (pVC p) (pDQ p) of
        Nothing -> Nothing
        Just (m, pDQ') -> Just (m, p
            { pVC = vcCombine (mVC m) (pVC p) -- Could use tick here.
            , pDQ = pDQ'
            , pHist = Deliver (pID p) m : pHist p
                `proofConst` internalDeliverCHA m (pID p) (pVC p) (pHist p)
            })
{-@ reflect internalDeliver @-}
{-# WARNING internalDeliver "Internal use only" #-}




-- ** Broadcast

-- | See 'CBCAST.broadcast'.
{-@
internalBroadcast :: r -> p:Process r -> (MasP r {p}, PasP r {p}) @-}
internalBroadcast :: r -> Process r -> (Message r, Process r)
internalBroadcast raw p₀ =
    let m = broadcastHelper_prepare raw p₀
        p₁ = broadcastHelper_inject m p₀
    in case internalDeliver p₁ `proofConst` broadcastAlwaysDelivers raw p₀ of
            Just tup -> tup
{-@ reflect internalBroadcast @-}
{-# WARNING internalBroadcast "Internal use only" #-}

{-@
broadcastHelper_prepare :: r -> p:Process r -> MasP r {p} @-}
broadcastHelper_prepare :: r -> Process r -> Message r
broadcastHelper_prepare raw p = Message
    { mVC = vcTick (pVC p) (pID p)
    , mSender = pID p
    , mRaw = raw
    }
{-@ reflect broadcastHelper_prepare @-}
{-# WARNING broadcastHelper_prepare "Internal use only" #-}

{-@
broadcastHelper_inject :: m:Message r -> PasM r {m} -> PasM r {m} @-}
broadcastHelper_inject :: Message r -> Process r -> Process r
broadcastHelper_inject m p = p
    { pDQ = m : pDQ p
    , pHist = Broadcast m : pHist p
        `proofConst` internalBroadcastCHA m (pVC p) (pHist p)
    }
{-@ reflect broadcastHelper_inject @-}
{-# WARNING broadcastHelper_inject "Internal use only" #-}




-- * Clock history agreement

{-@
internalDeliverCHA
    ::    m:Message r
    -> p_id:PIDasM {m}
    -> CHApreservation r {messageSize m} {vcCombine (mVC m)} {cons (Deliver p_id m)}
@-}
internalDeliverCHA :: Message r -> PID -> VC -> ProcessHistory r -> Proof
internalDeliverCHA m p_id p_vc p_hist =
    let
    p_vc' = vcCombine (mVC m) p_vc
    n = vcSize p_vc'
    e = Deliver p_id m
    in
        histVC n (e : p_hist)
    === mVC (eventMessage e) `vcCombine` histVC n p_hist
    === mVC m `vcCombine`  p_vc
    *** QED
{-# WARNING internalDeliverCHA "Verification only" #-}

{-@
internalBroadcastCHA
    :: m:Message r
    -> CHApreservation r {messageSize m} {identity} {cons (Broadcast m)} @-}
internalBroadcastCHA :: Message r -> VC -> ProcessHistory r -> Proof
internalBroadcastCHA m p_vc p_hist =
        histVC (vcSize p_vc) (Broadcast m : p_hist)
    === p_vc
    *** QED
{-# WARNING internalBroadcastCHA "Verification only" #-}




-- * Broadcast always delivers

-- | Broadcast's call to deliver will always return the message just produced
-- by the prepare message helper (not @Nothing@).
--
{-@ ple broadcastAlwaysDelivers @-}
{-@
broadcastAlwaysDelivers
    :: raw:r
    ->   p:Process r
    -> {
          isJust           (internalDeliver (broadcastHelper_inject (broadcastHelper_prepare raw p) p))
       &&
             fst (fromJust (internalDeliver (broadcastHelper_inject (broadcastHelper_prepare raw p) p)))
          ==                                                         broadcastHelper_prepare raw p
       }
@-}
broadcastAlwaysDelivers :: r -> Process r -> Proof
broadcastAlwaysDelivers raw p₀ =
    let
    m = broadcastHelper_prepare raw p₀
    p₁ = broadcastHelper_inject m p₀
        --- QQQ: Why does this step require PLE?
        === p₀
            { pDQ = m : pDQ p₀
            , pHist = Broadcast m : pHist p₀
                `proofConst` internalBroadcastCHA m (pVC p₀) (pHist p₀) -- CHA_MIGRATION
            }
    dequeueBody
        = dequeue (pVC p₁) (pDQ p₁)
        === dequeue (pVC p₁) (m : pDQ p₀)
            ? deliverableNewMessage raw p₀
        --- QQQ: Why does this step require PLE?
        === Just (m, pDQ p₀)
    deliverBody
        = internalDeliver p₁
        ? dequeueBody
        --- QQQ: Why does this step require PLE?
        === Just (m, p₁
            { pVC = vcCombine (mVC m) (pVC p₁)
            , pDQ = pDQ p₀
            , pHist = Deliver (pID p₁) m : pHist p₁
                `proofConst` internalDeliverCHA m (pID p₁) (pVC p₁) (pHist p₁) -- CHA_MIGRATION
            })
    in
    deliverBody *** QED
{-# WARNING broadcastAlwaysDelivers "Verification only" #-}

-- | Broadcast's prepare message helper produces messages deliverable at the
-- producing process process.
--
{-@ ple deliverableNewMessage @-}
{-@
deliverableNewMessage :: raw:_ -> p:_ -> {deliverable (broadcastHelper_prepare raw p) (pVC p)} @-}
deliverableNewMessage :: r -> Process r -> Proof
deliverableNewMessage raw p
    =   deliverable (broadcastHelper_prepare raw p) (pVC p) -- restate conclusion
    --- QQQ: Why does this step require PLE?
    === deliverable (Message (vcTick (pVC p) (pID p)) (pID p) raw) (pVC p) -- by definition of broadcastHelper_prepare
        ? deliverableAfterTick raw (pVC p) (pID p)
    *** QED
{-# WARNING deliverableNewMessage "Verification only" #-}
