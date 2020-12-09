{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
module Causal.CBCAST.ImplMonadic where

import Control.Monad.IO.Class (MonadIO)
import Control.Monad.Trans (MonadTrans)
import Control.Monad.Reader (MonadReader)
import Control.Monad.Writer (MonadWriter)
import Control.Monad.Catch (MonadThrow, MonadCatch, MonadMask)

import Control.Monad.State (StateT)
import qualified Control.Monad.State as State

import Causal.CBCAST.DelayQueue
import Causal.CBCAST.Message
import Causal.CBCAST.Process
import Causal.VectorClockSledge

-- * Implementation

-- ** Internal operations

-- | Monad transformer maintaining internal state.
type Internal r m a = StateT (Process r) m a

-- | Prepare to send a message.
--
--      "(1) Before sending m, process p_i increments VT(p_i)[i] and timestamps
--      m."
--
-- Since this modifies the vector clock, it could change the deliverability of
-- messages in the delay queue. Therefore 'internalDeliverReceived' must be run
-- after this.
internalSend :: Monad m => r -> Internal r m ()
internalSend r = do
    State.modify' $ \p -> p{pVT=vcTick (pNode p) (pVT p)}
    m <- Message <$> State.gets pNode <*> State.gets pVT <*> return r
    State.modify' $ \p -> p{pOutbox=fPush (pOutbox p) m}

-- | Receive a message. Delay its delivery or deliver it immediately. The
-- "until" part is handled by 'internalDeliverReceived'.
--
--      "(2) On reception of message m sent by p_i and timestamped with VT(m),
--      process p_j =/= p_i delays delivery of m until:
--
--          for-all k: 1...n { VT(m)[k] == VT(p_j)[k] + 1 if k == i
--                           { VT(m)[k] <= VT(p_j)[k]     otherwise
--
--      Process p_j need not delay messages received from itself. Delayed
--      messages are maintained on a queue, the CBCAST _delay queue_. This
--      queue is sorted by vector time, with concurrent messages ordered by
--      time of receipt (however, the queue order will not be used until later
--      in the paper)."
--
-- Since this modifies the vector clock in one case and the delay queue in the
-- other, it could change the deliverability of messages in the delay queue.
-- Therefore 'internalDeliverReceived' must be run after this.
internalReceive :: Monad m => Message r -> Internal r m ()
internalReceive m = do
    pid <- State.gets pNode
    if mSender m == pid
    -- "Process p_j need not delay messages received from itself."
    then internalDeliver m
    -- "Delayed messages are maintained on a queue, the CBCAST _delay queue_."
    else State.modify' $ \p -> p{pDQ=dqEnqueue m (pDQ p)}

-- | Deliver messages until there are none ready.
--
-- This algorithm delivers full groups of deliverable messages before checking
-- deliverability again. While this can't make anything undeliverable or break
-- causal order of deliveries, it does produce a slightly different delivery
-- order than an algorithm which checks deliverability after every delivery.
internalDeliverReceived :: Monad m => Internal r m ()
internalDeliverReceived =
    dqDequeue <$> State.gets pVT <*> State.gets pDQ >>= \case
        Just (dq, m) -> do
            State.modify' $ \p -> p{pDQ=dq}
            internalDeliver m
            internalDeliverReceived
        Nothing -> return ()

-- | Deliver a message.
--
--      "(3) When a message m is delivered, VT(p_j) is updated in accordance
--      with the vector time protocol from Section 4.3."
--
-- The relevant part of section 4.3 is:
--
--      "(4) When process p_j delivers a message m from process p_i
--      containing VT(m), p_j modifies its vector clock in the
--      following manner:
--
--          for-all k element-of 1...n: VT(p_j)[k] = max(VT(p_j)[k], VT(m)[k])"
--
-- Since this modifies the vector clock, it could change the deliverability of
-- messages in the delay queue. Therefore 'internalDeliverReceived' must be run
-- after this.
internalDeliver :: Monad m => Message r -> Internal r m ()
internalDeliver m = State.modify' $ \p -> p
    { pVT = vcCombine (pVT p) (mSent m)
    , pInbox = fPush (pInbox p) m
    }

-- ** External API

-- | Causal delivery monad transformer wrapper encapsulating internal state.
newtype CausalT r m a = CausalT (Internal r m a)
    deriving
    ( Functor, Applicative, Monad, MonadIO
--  , MonadBase IO
    , MonadTrans, MonadReader r, MonadWriter w--, MonadState s
    , MonadThrow, MonadCatch, MonadMask
--  , MonadTransControl, MonadBaseControl IO
    )

-- | Execute an action and maintain appropriate causal delivery state.
execCausalT :: Monad m => Process r -> CausalT r m () -> m (Process r)
execCausalT p (CausalT action) = State.execStateT action p

-- | Prepare a message for sending, possibly triggering the delivery of
-- messages in the delay queue.
send :: Monad m => r -> CausalT r m ()
send r = CausalT $ do
    internalSend r
    internalDeliverReceived

-- | Receive a message, possibly triggering the delivery of messages in the
-- delay queue.
receive :: Monad m => Message r -> CausalT r m ()
receive m = CausalT $ do
    internalReceive m
    internalDeliverReceived

-- | Remove and return all sent messages so the application can broadcast them
-- (in sent-order, eg, with 'mapM_').
drainBroadcasts :: Monad m => CausalT r m [Message r]
drainBroadcasts = CausalT $ do
    xs <- State.gets pOutbox
    State.modify' $ \p -> p{pOutbox=fNew}
    return (fList xs)

-- | Remove and return all delivered messages so the application can process
-- them (in delivered-order, eg, with 'fmap').
drainDeliveries :: Monad m => CausalT r m [Message r]
drainDeliveries = CausalT $ do
    xs <- State.gets pInbox
    State.modify' $ \p -> p{pInbox=fNew}
    return (fList xs)

-- * Verification

{-@ lazy internalDeliverReceived @-} -- FIXME: given the type of internalDeliverReceived, it's not clear how to specify the decreasing parameter
