module Causal.CBCAST.Process where

import Causal.CBCAST.DelayQueue
import Causal.CBCAST.Message
import Causal.VectorClockConcrete

type DQ r = DelayQueue r

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
    , pDQ :: DQ r
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
