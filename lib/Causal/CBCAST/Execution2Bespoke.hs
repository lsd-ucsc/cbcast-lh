{-# LANGUAGE NamedFieldPuns #-}
module Causal.CBCAST.Execution2Bespoke where

import Language.Haskell.Liquid.ProofCombinators
import Redefined

-- data DAG
--     = DAGnil
--     | DAGcons
--         { gTail :: DAG
--         , gHead :: Set (Fin {gSize gTail})
--         }

-- data Event pid msg
--     = Broadcast pid msg -- Process pid sends message msg to everyone.
--     | Deliver pid msg -- Process pid delivers message msg to itself.

-- | Define a cons-list of execution events, each referencing by index some previous events.
data Execution pid msg
    = ExNil
    | ExBroadcast
        { ebSender :: pid
        , ebMessage :: msg
        , ebTail :: Execution pid msg
        , ebPreviousEvent :: Maybe Fin
        }
    | ExDeliver
        { edReceiver :: pid
        , edTail :: Execution pid msg
        , edPreviousEvent :: Maybe Fin
        , edBroadcastEvent :: Fin
        }
{-@
data Execution [executionSize] pid msg
    = ExNil
    | ExBroadcast
        { ebSender :: pid
        , ebMessage :: msg
        , ebTail :: Execution pid msg
        , ebPreviousEvent :: PreviousEvent {ebTail} {ebSender}
        }
    | ExDeliver
        { edReceiver :: pid
        , edTail :: Execution pid msg
        , edPreviousEvent :: PreviousEvent {edTail} {edReceiver}
        , edBroadcastEvent :: BroadcastEvent {edTail} {edReceiver}
        }
@-}
-- [x] Enforce DAG by constraining the Fin of event fields to reference into the tail of the cons-list.
-- [x] Enforce Deliver{edBroadcastEvent} references Broadcast from distinct-process
-- [x] Enforce Deliver{edPreviousEvent} references own-process-event unless there are none
--      - [ ] MOST RECENT
-- [x] Enforce Broadcast{ebPreviousEvent} references own-process-event unless there are none
--      - [ ] MOST RECENT

-- An integer index to event in the execution.
{-@ type Edge EX = Fin {executionSize EX} @-}

-- An event in the execution at the specified process.
{-@ type SelfEdge EX PID = { e : Edge {EX} | eventProcess (executionLookup EX e) == PID } @-}

-- An event in the execution at a distinct process.
{-@ type OtherEdge EX PID = { e : Edge {EX} | eventProcess (executionLookup EX e) /= PID } @-}

-- A value required except when there are no events in the execution at the specified process.
{-@ type Optional a EX PID = { m : Maybe a | m == Nothing => not (hasProcess EX PID) } @-}

-- Process-order edge.
{-@ type PreviousEvent EX PID = Optional (SelfEdge {EX} {PID}) {EX} {PID} @-}

-- Happens-before edge.
{-@ type BroadcastEvent EX PID = OtherEdge {EX} {PID} @-}

-- | How many events are in the execution?
{-@ measure executionSize @-}
{-@ executionSize :: Execution pid msg -> Nat @-}
executionSize :: Execution pid msg -> Int
executionSize ExNil = 0
executionSize ExBroadcast{ebTail} = 1 + executionSize ebTail
executionSize ExDeliver{edTail} = 1 + executionSize edTail

-- Ask LH to add an extra assertion everywhere: An execution has nonzero size IFF it is non-nil.
{-@
using (Execution pid msg) as
    { ex : Execution pid msg |
        0 < executionSize ex <=> ex /= ExNil
    }
@-}

-- | Return the part of the execution which recorded before the current event.
{-@ reflect executionTail @-}
{-@ executionTail :: {ex:Execution pid msg | ex /= ExNil} -> {out:Execution pid msg | executionSize ex == 1 + executionSize out} @-}
executionTail :: Execution pid msg -> Execution pid msg
executionTail ExBroadcast{ebTail} = ebTail
executionTail ExDeliver{edTail} = edTail

-- | Return the specified event by indexing into the execution.
{-@ reflect executionLookup @-}
{-@ executionLookup :: ex:Execution pid msg -> i:Fin {executionSize ex} -> {out:Execution pid msg | out /= ExNil} @-}
executionLookup :: Execution pid msg -> Fin -> Execution pid msg
executionLookup ex i
    | executionSize exTail == i = ex
    | otherwise = executionLookup exTail i
  where
    exTail = executionTail ex

-- | On which process did the event occur?
{-@ reflect eventProcess @-}
{-@ eventProcess :: {ex:Execution pid msg | ex /= ExNil} -> pid @-}
eventProcess :: Execution pid msg -> pid
eventProcess ExBroadcast{ebSender} = ebSender
eventProcess ExDeliver{edReceiver} = edReceiver

-- | Does the execution include the process?
{-@ reflect hasProcess @-}
hasProcess :: Eq pid => Execution pid msg -> pid -> Bool
hasProcess ExNil _p = False
hasProcess ex p = eventProcess ex == p || hasProcess (executionTail ex) p
