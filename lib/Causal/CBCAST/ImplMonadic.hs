{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
module Causal.CBCAST.ImplMonadic where

-- page 7/278:
--
--      "The execution of a process is a partial ordered sequence of _events_,
--      each corresponding to the execution of an indivisible action. An
--      acyclic event order, denoted ->^p, reflects the dependence of events
--      occuring at process p upon one another."
--
--      "As Lamport [17], we define the potential causality relation for the
--      system, ->, as the transitive closure of the relation defined as
--      follows:
--
--      (1) if there-exists p: e ->^p e' then e -> e'
--      (2) for-all m: send(m) -> rcv(m)"
--
-- page 8/279:
--
--      "Two types of delivery ordering will be of interest here. We define the
--      causal delivery ordering for multicast messages m and m' as follows:
--
--          m -> m' => for-all p element-of dests(m) intersect dests(m'):
--                      deliver(m) ->^p deliver(m')
--
--      CBCAST provides only th ecausal delivery ordering."
--
-- page 10/281:
--
--      "Suppose that a set of processes P communicate using only broadcasts to
--      the full set of processes in the system; that is,
--      for-all m: dests(m) = P."
--
--      "We now develop a _delivery protocol_ by which each process p receives
--      messages sent to it, delays them if necessary, and then delivers them
--      in an order consistent with causality:
--
--          m -> m' => for-all p: deliver_p(m) ->^p deliver_p(m')

--import Language.Haskell.Liquid.ProofCombinators (Proof, trivial)

import Control.Monad.IO.Class (MonadIO)
import Control.Monad.Trans (MonadTrans)
import Control.Monad.Reader (MonadReader)
import Control.Monad.Writer (MonadWriter)
import Control.Monad.Catch (MonadThrow, MonadCatch, MonadMask)

import Control.Monad.State (StateT)
import qualified Control.Monad.State as State

import Causal.CBCAST.Message (PID, VT, Message(..))
import Causal.CBCAST.DelayQueue
import Causal.VectorClockConcrete

-- * Internal data structures

-- | Trivial fifo. Appended to it with 'fPush'. Dump it out with 'fList' and
-- map over the result in fifo order. Replace it after dumping with 'fNew'.
-- >>> fList $ fPush (fPush (fPush fNew 'a') 'b') 'c'
-- "abc"
-- >>> fList $ fNew `fPush` 'a' `fPush` 'b' `fPush` 'c'
-- "abc"
newtype FIFO a = FIFO [a]
fNew :: FIFO a
fNew = FIFO []
fPush :: FIFO a -> a -> FIFO a
fPush (FIFO xs) x = FIFO (x:xs)
fList :: FIFO a -> [a]
fList (FIFO xs) = reverse xs

-- | CBCAST process state with ID, logical clock, and delay queue. The inbox
-- stores messages which are delivered, and the outbox stores messages which
-- are ready to broadcast.
data Process r = Process
    { pNode :: PID
    , pVT :: VT
    , pDQ :: DelayQueue r
    , pInbox :: FIFO (Message r)
    , pOutbox :: FIFO (Message r)
    }

-- | New empty process using the given process ID.
pNew :: PID -> Process r
pNew pid = Process
    { pNode = pid
    , pVT = vcNew
    , pDQ = dqNew
    , pInbox = fNew
    , pOutbox = fNew
    }

-- | Monad transformer maintaining internal state.
type Internal r m a = StateT (Process r) m a

-- * Internal operations

-- | Prepare to send a message.
--
--      "(1) Before sending m, process p_i increments VT(p_i)[i] and timestamps
--      m."
--
-- Since this modifies the vector clock, it could change the deliverability of
-- messages in the delay queue. Therefore 'cbcastDeliverReceived' must be run
-- after this.
cbcastSend :: Monad m => r -> Internal r m ()
cbcastSend r = do
    State.modify' $ \p -> p{pVT=vcTick (pNode p) (pVT p)}
    m <- Message <$> State.gets pNode <*> State.gets pVT <*> return r
    State.modify' $ \p -> p{pOutbox=fPush (pOutbox p) m}

-- | Receive a message. Delay its delivery or deliver it immediately. The
-- "until" part is handled by 'cbcastDeliverReceived'.
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
-- Therefore 'cbcastDeliverReceived' must be run after this.
cbcastReceive :: Monad m => Message r -> Internal r m ()
cbcastReceive m = do
    pid <- State.gets pNode
    if mSender m == pid
    -- "Process p_j need not delay messages received from itself."
    then cbcastDeliver m
    -- "Delayed messages are maintained on a queue, the CBCAST _delay queue_."
    else State.modify' $ \p -> p{pDQ=dqEnqueue m (pDQ p)}

-- | Deliver messages until there are none ready.
cbcastDeliverReceived :: Monad m => Internal r m ()
cbcastDeliverReceived = dqDequeue <$> State.gets pVT <*> State.gets pDQ >>= \case
    Just (dq, m) -> do
        State.modify' $ \p -> p{pDQ=dq}
        cbcastDeliver m
        cbcastDeliverReceived
    Nothing -> return ()
{-@ lazy cbcastDeliverReceived @-} -- FIXME; probably need to know that this terminates

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
-- messages in the delay queue. Therefore 'cbcastDeliverReceived' must be run
-- after this.
cbcastDeliver :: Monad m => Message r -> Internal r m ()
cbcastDeliver m = State.modify' $ \p -> p
    { pVT = vcCombine (pVT p) (mSent m)
    , pInbox = fPush (pInbox p) m
    }

-- * External API

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
    cbcastSend r
    cbcastDeliverReceived

-- | Receive a message, possibly triggering the delivery of messages in the
-- delay queue.
receive :: Monad m => Message r -> CausalT r m ()
receive m = CausalT $ do
    cbcastReceive m
    cbcastDeliverReceived

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
