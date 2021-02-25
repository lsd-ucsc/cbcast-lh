{-# LANGUAGE NamedFieldPuns #-}
module Causal.CBCAST.Process
( module Causal.CBCAST.Process
, module Redefined
) where

import Redefined
import Causal.VectorClock
import Causal.CBCAST.Message
import Causal.CBCAST.DelayQueue


-- * FIFO

-- | Trivial fifo. Appended to it with 'fPush'. Dump it out with 'fList' and
-- map over the result in fifo order. Replace it after dumping with 'fNew'.
-- >>> fList $ fPush (fPush (fPush fNew 'a') 'b') 'c'
-- "abc"
-- >>> fList $ fNew `fPush` 'a' `fPush` 'b' `fPush` 'c'
-- "abc"
{-@
data FIFO [fSize]
          a = FIFO [a] @-}
data FIFO a = FIFO [a]
-- FIXME (NEWTYPE_RESTRICTION)

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


-- * Process

-- | CBCAST process state with ID, logical clock, and delay queue. The inbox
-- stores messages which are delivered, and the outbox stores messages which
-- are ready to broadcast.
{-@
data Process [pSize]
             r = Process { pID::PID, pVC::VC, pDQ::DQ r {pID}, pInbox::FIFO (Message r), pOutbox::FIFO (Message r) } @-}
data Process r = Process { pID::PID, pVC::VC, pDQ::DQ r      , pInbox::FIFO (Message r), pOutbox::FIFO (Message r) }

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

-- | For calls into the Verification module's code.
{-@ measure pProc@-}
pProc :: Process r -> Proc
pProc Process{pID, pVC} = Proc{procId=pID, procVc=pVC}
