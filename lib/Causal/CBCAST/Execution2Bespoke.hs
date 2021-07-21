{-# LANGUAGE NamedFieldPuns #-}
module Causal.CBCAST.Execution2Bespoke where

import Language.Haskell.Liquid.ProofCombinators
import Redefined

-- | Define a cons-list of execution events, each referencing by index
-- (executionLookup) some previous events to form a DAG.
data Execution pid msg
    = ExNil
    | ExBroadcast
        { broadcastSender :: pid
        , broadcastMessage :: msg
        , bExecutionTail :: Execution pid msg
        , bPreviousProcessEvent :: Maybe Fin
        }
    | ExDeliver
        { deliverReceiver :: pid
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
        , bPreviousProcessEvent :: ProcessOrderEvent {bExecutionTail} {broadcastSender}
        }
    | ExDeliver
        { deliverReceiver :: pid
        , dExecutionTail :: Execution pid msg
        , dPreviousProcessEvent :: ProcessOrderEvent {dExecutionTail} {deliverReceiver}
        , dMessageBroadcastEvent :: MessageSendEvent {dExecutionTail} {deliverReceiver}
        }
@-}

-- | Enforce that bPreviousProcessEvent, dPreviousProcessEvent, and
-- dMessageBroadcastEvent form a DAG over indexes (executionLookup) to all the
-- events in the list by constraining them to refernce only events in
-- bExecutionTail or dExecutionTail respectively.
--
-- Additionally enforce that bPreviousProcessEvent and dPreviousProcessEvent
-- both reference the most-recent-event on the process with PID broadcastSender
-- or deliverReceiver, respectively, iff such an event exists.
--
-- Finally enforce that dMessageBroadcastEvent references a broadcast event on
-- a distinct process from deliverReceiver.
--
{-@
type Edge EX = Fin {executionSize EX}

type EdgeToProcess EX PID =
    { e : Edge {EX}
    | eventProcess (executionLookup EX e) == PID }
type MostRecentEventOnProcess EX PID =
    { e : EdgeToProcess {EX} {PID}
    | e == executionSize (latestProcessEvent EX PID) }
type OptionalIfNoProcessEvents a EX PID =
    { m : Maybe a
    | hasProcess EX PID <=> isJust m }
type ProcessOrderEvent EX PID =
    OptionalIfNoProcessEvents (MostRecentEventOnProcess {EX} {PID}) {EX} {PID}

type EdgeToDistinct EX PID =
    { e : Edge {EX}
    | eventProcess (executionLookup EX e) /= PID }
type MessageSendEvent EX PID =
    { e : EdgeToDistinct {EX} {PID}
    | isBroadcast (executionLookup EX e) }
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
{-@ reflect isBroadcast @-}
isBroadcast :: Execution pid msg -> Bool
isBroadcast ExBroadcast{} = True
isBroadcast _ = False

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
{-@ reflect hasProcess @-}
hasProcess :: Eq pid => Execution pid msg -> pid -> Bool
hasProcess ExNil _p = False
hasProcess ex p = eventProcess ex == p || hasProcess (executionTail ex) p

{-@ hasProcessImpliesNonNil :: ex:Execution pid msg -> {p:pid | hasProcess ex p} -> {ex /= ExNil} @-}
hasProcessImpliesNonNil :: Execution pid msg -> pid -> Proof
hasProcessImpliesNonNil _ _ = {-@ ple hasProcessImpliesNonNil @-} ()

{-@ hasProcessAndNotHeadThenTailHasProcess :: ex:Execution pid msg -> {p:pid | hasProcess ex p && not (eventProcess ex) == p} -> {hasProcess (executionTail ex) p} @-}
hasProcessAndNotHeadThenTailHasProcess :: Execution pid msg -> pid -> Proof
hasProcessAndNotHeadThenTailHasProcess _ _ = {-@ ple hasProcessAndNotHeadThenTailHasProcess @-} ()

-- | Return the latest event in the execution occuring on the process.
{-@ reflect latestProcessEvent @-}
{-@ latestProcessEvent :: ex:Execution pid msg -> {p:pid | hasProcess ex p} -> Execution pid msg @-}
latestProcessEvent :: Eq pid => Execution pid msg -> pid -> Execution pid msg
latestProcessEvent ex p
    | p == eventProcess ex' = ex'
    | otherwise = let
            p' = p `with` hasProcessAndNotHeadThenTailHasProcess ex p
        in latestProcessEvent (executionTail ex') p'
  where
    ex' = ex `with` hasProcessImpliesNonNil ex p

-- | Add proof evidence to the context of a variable.
{-@ inline with @-}
{-@ with :: x:a -> b -> {y:a | x == y} @-}
with :: a -> b -> a
with x _ = x
