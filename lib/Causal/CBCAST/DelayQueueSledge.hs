{-# LANGUAGE NamedFieldPuns #-}
module Causal.CBCAST.DelayQueueSledge where

-- import Redefined

import Causal.CBCAST.Message
import qualified Causal.VectorClockSledge as VC


-- * Types

data DelayQueue r
    = Nil
    | DQ
        { dqMessage :: Message r
        , dqRest    :: DelayQueue r
        }
{-@
data DelayQueue [dqSize] r where
      Nil :: DelayQueue r
    | DQ :: m:Message r -> {rest:DelayQueue r | mLEQdq m rest} -> DelayQueue r
@-}


-- * Logical predicates

{-@
dqSize :: _ -> Nat @-}
dqSize :: DelayQueue r -> Int
dqSize Nil = 0
dqSize DQ{dqRest} = 1 + dqSize dqRest
{-@ measure dqSize @-}

-- | Predicate: Are the messages sorted as a delay-queue list specifies?
mLEQ :: Message r -> Message r -> Bool
mLEQ a b = VC.vcLessEqual (mSent a) (mSent b)
{-@ inline mLEQ @-}

-- | Predicate: Is the message sorted with respect to the delay-queue list?
mLEQdq :: Message r -> DelayQueue r -> Bool
mLEQdq _ Nil = True
mLEQdq m DQ{dqMessage} = mLEQ m dqMessage
{-@ inline mLEQdq @-}


-- * User API


-- TRY REWRITING THIS TO CALL mLEQdq (the ordering invariant)

--dqEnqueueImpl :: Message r -> DelayQueue r -> DelayQueue r
--dqEnqueueImpl m dq = case dq of
--    Nil                                     -> new
--    DQ{dqMessage,dqRest}
--                         | m `mLEQdq` dq -> dq{dqRest=dqEnqueueImpl m dqRest}
--                         | otherwise     -> new{dqRest=dq}
----dqEnqueueImpl m (x:xs)
----    | mSent x `vcLessEqual` mSent m = x : dqEnqueueImpl m xs
----    | otherwise = m : x:xs
--  where
--    new = DQ m Nil
