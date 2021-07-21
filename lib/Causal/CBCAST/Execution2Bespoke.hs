{-# LANGUAGE NamedFieldPuns #-}
module Causal.CBCAST.Execution2Bespoke where

import Language.Haskell.Liquid.ProofCombinators
import Redefined

-- | Define a cons-list of execution events. Use two cons-tructors to represent
-- broadcast and deliver events in the execution. Each cons-cell has the
-- execution tail and also references by index (executionLookup) some previous
-- events to form a DAG.
--
--  * Enforce that bPreviousProcessEvent, dPreviousProcessEvent, and
--    dMessageBroadcastEvent form a DAG over all the events in the list by
--    constraining them to reference only events in bExecutionTail or
--    dExecutionTail respectively.
--
--  * Additionally enforce that bPreviousProcessEvent and dPreviousProcessEvent
--    both reference the most-recent-event on the process with PID
--    broadcastSender or deliverReceiver, respectively, iff such an event exists.
--
--  * Finally enforce that dMessageBroadcastEvent references a broadcast event
--    on a distinct process from deliverReceiver.
--
data Execution pid msg
    = ExNil
    | ExBroadcast
        { broadcastSender :: pid -- Process where this event occurs.
        , broadcastMessage :: msg -- Message sent by this event.
        , bExecutionTail :: Execution pid msg
        , bPreviousProcessEvent :: Maybe Fin
        }
    | ExDeliver
        { deliverReceiver :: pid -- Process where this event occurs.
        , dExecutionTail :: Execution pid msg
        , dPreviousProcessEvent :: Maybe Fin
        , dMessageBroadcastEvent :: Fin
        }
{-@
data Execution [executionSize] pid msg
    = ExNil
    | ExBroadcast
        { broadcastSender :: pid
        , broadcastMessage :: msg
        , bExecutionTail :: Execution pid msg
        , bPreviousProcessEvent :: PreviousProcessEvent {bExecutionTail} {broadcastSender}
        }
    | ExDeliver
        { deliverReceiver :: pid
        , dExecutionTail :: Execution pid msg
        , dPreviousProcessEvent :: PreviousProcessEvent {dExecutionTail} {deliverReceiver}
        , dMessageBroadcastEvent :: MessageBroadcastEvent {dExecutionTail} {deliverReceiver}
        }
@-}

{-@
type Edge EX = Fin {executionSize EX}

type PreviousProcessEvent EX PID =
    { m : Maybe
            ({ e : Edge {EX}
                 | e == executionSize (executionLastestProcessEvent EX PID)
                && PID == eventProcess (executionLookup EX e)
            })
        | executionHasProcess EX PID <=> isJust m
    }

type MessageBroadcastEvent EX PID =
    { e : Edge {EX}
        | PID /= eventProcess (executionLookup EX e)
       && eventIsBroadcast (executionLookup EX e)
    }
@-}

-- | How many events are in the execution?
{-@ measure executionSize @-}
{-@ executionSize :: Execution pid msg -> Nat @-}
executionSize :: Execution pid msg -> Int
executionSize ExNil = 0
executionSize ExBroadcast{bExecutionTail} = 1 + executionSize bExecutionTail
executionSize ExDeliver{dExecutionTail} = 1 + executionSize dExecutionTail

-- | Return the part of the execution which recorded before the current event.
{-@ reflect executionTail @-}
{-@ executionTail :: {ex:Execution pid msg | ex /= ExNil} -> {out:Execution pid msg | executionSize ex == 1 + executionSize out} @-}
executionTail :: Execution pid msg -> Execution pid msg
executionTail ExBroadcast{bExecutionTail} = bExecutionTail
executionTail ExDeliver{dExecutionTail} = dExecutionTail

-- | On which process did the event occur?
{-@ reflect eventProcess @-}
{-@ eventProcess :: {ex:Execution pid msg | ex /= ExNil} -> pid @-}
eventProcess :: Execution pid msg -> pid
eventProcess ExBroadcast{broadcastSender} = broadcastSender
eventProcess ExDeliver{deliverReceiver} = deliverReceiver

-- | Is this event a broadcast?
{-@ reflect eventIsBroadcast @-}
eventIsBroadcast :: Execution pid msg -> Bool
eventIsBroadcast ExBroadcast{} = True
eventIsBroadcast _ = False

-- Ask LH to add an extra assertion everywhere: An execution has nonzero size IFF it is non-nil.
{-@
using (Execution pid msg) as
    { ex : Execution pid msg |
        0 < executionSize ex <=> ex /= ExNil
    }
@-}

-- | Return the specified event by indexing into the execution.
{-@ reflect executionLookup @-}
{-@ executionLookup :: ex:Execution pid msg -> i:Fin {executionSize ex} -> {out:Execution pid msg | out /= ExNil} @-}
executionLookup :: Execution pid msg -> Fin -> Execution pid msg
executionLookup ex i
    | executionSize exTail == i = ex
    | otherwise = executionLookup exTail i
  where
    exTail = executionTail ex

-- | Does the execution include the process?
{-@ reflect executionHasProcess @-}
executionHasProcess :: Eq pid => Execution pid msg -> pid -> Bool
executionHasProcess ExNil _p = False
executionHasProcess ex p = eventProcess ex == p || executionHasProcess (executionTail ex) p

{-@ hasProcessImpliesNonNil :: ex:Execution pid msg -> {p:pid | executionHasProcess ex p} -> {ex /= ExNil} @-}
hasProcessImpliesNonNil :: Execution pid msg -> pid -> Proof
hasProcessImpliesNonNil _ _ = {-@ ple hasProcessImpliesNonNil @-} ()

{-@ hasProcessAndNotHeadThenTailHasProcess :: ex:Execution pid msg -> {p:pid | executionHasProcess ex p && not (eventProcess ex) == p} -> {executionHasProcess (executionTail ex) p} @-}
hasProcessAndNotHeadThenTailHasProcess :: Execution pid msg -> pid -> Proof
hasProcessAndNotHeadThenTailHasProcess _ _ = {-@ ple hasProcessAndNotHeadThenTailHasProcess @-} ()

-- | Return the latest event in the execution occuring on the process.
{-@ reflect executionLastestProcessEvent @-}
{-@ executionLastestProcessEvent :: ex:Execution pid msg -> {p:pid | executionHasProcess ex p} -> Execution pid msg @-}
executionLastestProcessEvent :: Eq pid => Execution pid msg -> pid -> Execution pid msg
executionLastestProcessEvent ex p
    | p == eventProcess ex' = ex'
    | otherwise = let
            p' = p `with` hasProcessAndNotHeadThenTailHasProcess ex p
        in executionLastestProcessEvent (executionTail ex') p'
  where
    ex' = ex `with` hasProcessImpliesNonNil ex p

-- | Add proof evidence to the context of a variable.
{-@ inline with @-}
{-@ with :: x:a -> b -> {y:a | x == y} @-}
with :: a -> b -> a
with x _ = x
