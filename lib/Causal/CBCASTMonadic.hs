{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Causal.CBCASTMonadic where

-- This module uses a monadic pattern where the callback is a bit iffy because
-- it can send during processing of a message delivery.
-- ===========================================================================

-- page 7/278:
--
--      "The execution of a process is a partiall ordered sequence of _events_,
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
import Control.Arrow (first, second)

import Control.Monad.IO.Class (MonadIO)
import Control.Monad.Trans (MonadTrans)
--import Control.Monad.Reader (MonadReader)
--import Control.Monad.Writer (MonadWriter)
--import Control.Monad.State (MonadState)
import Control.Monad.Catch (MonadThrow, MonadCatch, MonadMask)

import Control.Monad.RWS (RWST)
import qualified Control.Monad.RWS as RWS

import Causal.CBCAST.Message (PID, VT, Message(..))
import Causal.CBCAST.DelayQueue
import Causal.VectorClockConcrete

-- | Prepare a message for sending, possibly triggering the delivery of
-- messages in the delay-queue. Callers are responsible for broadcasting the
-- packaged message and then processing their results from any deliveries which
-- may occurred.
send :: Monad m => AcceptT r m a -> r -> CausalT r m [a]
send uAccept r = do
    cbcastSend r
    deliveryLifecycle uAccept

-- | Receive a message, possibly triggering the delivery of messages in the
-- delay-queue. Callers are responsible for processing the results from any
-- deliveries which may have occurred.
receive :: Monad m => AcceptT r m a -> Message r -> CausalT r m [a]
receive uAccept m = do
    x <- cbcastReceive uAccept m
    xs <- deliveryLifecycle uAccept
    return (maybe xs (:xs) x)

-- | Deliver messages until there are none ready.
deliveryLifecycle :: Monad m => AcceptT r m a -> CausalT r m [a]
deliveryLifecycle uAccept = do
    st <- CausalT RWS.get
    case uncurry dqDequeue st of
        Just (dq, m) -> do
            CausalT $ RWS.modify' (second (const dq))
            x <- cbcastDeliver uAccept m
            xs <- deliveryLifecycle uAccept
            return (x:xs)
        Nothing -> return []
{-@ lazy deliveryLifecycle @-} -- FIXME; probably need to know that this terminates

-----------------

type DQ r = DelayQueue r

newtype CausalT r m a = CausalT (RWST PID [Message r] (VT, DQ r) m a)
    deriving
    ( Functor, Applicative, Monad, MonadIO
--  , MonadBase IO
    , MonadTrans--, MonadReader r, MonadWriter w, MonadState s
    , MonadThrow, MonadCatch, MonadMask
--  , MonadTransControl, MonadBaseControl IO
    )

-- | User function. Accept a message with metadata and return some result which
-- orchestration hands back to the user code. 
type AcceptT r m a = Message r -> CausalT r m a

-- | Prepare to send a message.
--
--      "(1) Before sending m, process p_i increments VT(p_i)[i] and timestamps
--      m."
--
-- Since this modifies the vector-clock and could change the deliverability of
-- messages in the delay-queue, the delivery lifecycle must be run after this.
cbcastSend :: Monad m => r -> CausalT r m () -- (Process r, Message r)
cbcastSend r = CausalT $ do
    pid <- RWS.ask
    RWS.modify' (first (pid `vcTick`))
    vt <- RWS.gets fst
    RWS.tell [Message{mSender=pid, mSent=vt, mRaw=r}]

-- | Receive a message. Delay its delivery on a queue or deliver it
-- immediately. The "until" part is handled by 'deliveryLifecycle'.
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
-- Since this modifies the vector-clock in one case and the delay-queue in the
-- other, it could change the deliverability of messages in the delay-queue,
-- the delivery lifecycle must be run after this.
cbcastReceive :: Monad m => AcceptT r m a -> Message r -> CausalT r m (Maybe a)
cbcastReceive uAccept m = do
    pid <- CausalT RWS.ask
    if mSender m == pid
    -- "Process p_j need not delay messages received from itself."
    then fmap pure (cbcastDeliver uAccept m)
    -- "Delayed messages are maintained on a queue, the CBCAST _delay queue_."
    else CausalT $ do
        RWS.modify' (second (dqEnqueue m))
        return Nothing

-- | Deliver a message by calling a user supplied function.
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
-- Since this modifies the vector-clock and could change the deliverability of
-- messages in the delay-queue, the delivery lifecycle must be run after this.
cbcastDeliver :: Monad m => AcceptT r m a -> Message r -> CausalT r m a
cbcastDeliver uAccept m = do
    CausalT $ RWS.modify' (first (`vcCombine` mSent m))
    uAccept m
