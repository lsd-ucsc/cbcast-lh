{-# LANGUAGE NamedFieldPuns #-}
module Causal.CBCAST.Process where

import Redefined
import Causal.CBCAST.VectorClock
import Causal.CBCAST.Message
import Causal.CBCAST.DelayQueue


-- * FIFO

-- | Trivial fifo. Appended to it with 'fPush'. Dump it out with 'fList' and
-- map over the result in fifo order. Replace it after dumping with 'fNew'.
--
-- >>> fList $ fPush (fPush (fPush fNew 'a') 'b') 'c'
-- "abc"
-- >>> fList $ fNew `fPush` 'a' `fPush` 'b' `fPush` 'c'
-- "abc"
--
-- >>> import Control.Arrow (second)
-- >>> second fList $ fPop $ fNew `fPush` 'a' `fPush` 'b' `fPush` 'c'
-- ('a',"bc")
{-@
data FIFO [fSize]
          a = FIFO [a] @-}
data FIFO a = FIFO [a]

fSize :: FIFO a -> Int
fSize (FIFO xs) = listLength xs
{-@ measure fSize @-}

fNew :: FIFO a
fNew = FIFO []
{-@ inline fNew @-}

fPush :: FIFO a -> a -> FIFO a
fPush (FIFO xs) x = FIFO (x:xs)
{-@ inline fPush @-}

fList :: FIFO a -> [a]
fList (FIFO xs) = listReverse xs
{-@ inline fList @-}

-- | Pops the first item pushed.
{-@ fPop :: {xs:FIFO a | 0 < fSize xs} -> (a, FIFO a) @-}
fPop :: FIFO a -> (a, FIFO a)
fPop (FIFO xs) = let (ys, y) = listInitLast xs in (y, FIFO ys)
{-@ inline fPop @-}


-- * Process

-- | CBCAST process state with ID, logical clock, and delay queue. The inbox
-- stores messages which are delivered, and the outbox stores messages which
-- are ready to broadcast.
{-@
data Process [pSize]
             r = Process { pID::PID, pVC::VC, pDQ::DQ r      , pInbox::FIFO (Message r), pOutbox::FIFO (Message r) } @-}
data Process r = Process { pID::PID, pVC::VC, pDQ::DQ r      , pInbox::FIFO (Message r), pOutbox::FIFO (Message r) }
-- TODO: use invariant to enforce that outbox only contains messages with own sender id
-- TODO: use invariant to enforce that DQ excludes messages with own sender id

pSize :: Process r -> Int
pSize Process{pDQ, pInbox, pOutbox} = dqSize pDQ + fSize pInbox + fSize pOutbox
{-@ measure pSize @-}

-- | Alternate measure for the 'DelayQueue' of a 'Process'
{-@
pdqSize :: _ -> Nat @-}
pdqSize :: Process r -> Int
pdqSize Process{pDQ} = dqSize pDQ
{-@ measure pdqSize @-}

-- | New empty process using the given process ID.
{-@ ple pNew @-}
{-@
pNew :: PID -> ProcCount -> Process r @-}
pNew :: PID -> Int -> Process r
pNew pid pCount = Process
    { pID = pid
    , pVC = vcNew pCount
    , pDQ = dqNew
    , pInbox = fNew
    , pOutbox = fNew
    }
{-@ inline pNew @-}
