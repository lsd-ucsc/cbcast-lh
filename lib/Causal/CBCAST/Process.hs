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
-- >>> fmap (second fList) . fPop $ fNew `fPush` 'a' `fPush` 'b' `fPush` 'c'
-- Just ('a',"bc")
{-@
data FIFO [fSize]
          a = FIFO [a] @-}
data FIFO a = FIFO [a]
    deriving (Eq, Show)

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
fPop :: FIFO a -> Maybe (a, FIFO a)
fPop (FIFO []) = Nothing
fPop (FIFO xs) = Just $ let (ys, y) = listInitLast xs in (y, FIFO ys)
{-@ inline fPop @-}


-- * Process

-- | CBCAST process state with ID, logical clock, and delay queue.
--
-- 'pToSelf' and 'pToNetwork' store copies of messages which were sent by the
-- current process, for the named purposes.
{-@
data Process r = Process
    { pID :: PID
    , pVC :: VC
    , pDQ :: DQ r {pID}
    , pToSelf :: FIFO ({m:Message r | pID == mSender m})
    , pToNetwork :: FIFO ({m:Message r | pID == mSender m})
    }
@-}
data Process r = Process
    { pID :: PID
    , pVC :: VC
    , pDQ :: DQ r
    , pToSelf :: FIFO (Message r)
    , pToNetwork :: FIFO (Message r)
    }
    deriving (Eq, Show)

-- | New empty process using the given process ID.
{-@ ple pNew @-}
{-@
pNew :: PID -> ProcCount -> Process r @-}
pNew :: PID -> Int -> Process r
pNew pid pCount = Process
    { pID = pid
    , pVC = vcNew pCount
    , pDQ = dqNew pid
    , pToSelf = fNew
    , pToNetwork = fNew
    }
{-@ inline pNew @-}
