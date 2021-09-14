module Causal.Execution.Type where

import Redefined.Bool
import Redefined.Tuple
import Redefined.List
import Redefined.Set

import Data.Assoc
import Data.BinaryRelation


-- * Event type

-- | Events which may occur on a process.
data Event p m
    = Broadcast {broadcastMessage::m} -- ^ broadcast(m)
    | Deliver {deliverProcess::p, deliverMessage::m} -- ^ deliver_p(m)
    deriving (Eq, Ord)
{-@
data Event p m
    = Broadcast {broadcastMessage::m}
    | Deliver {deliverProcess::p, deliverMessage::m}
@-} -- To create measures for each field.


-- * Process-state type

-- | Events in reverse-order of their taking place on the process. New events
-- are cons'd to the left. The tail is prior process state.
type ProcessState p m = [Event p m]

{-@ priorState :: {s:ProcessState p m | s /= []} -> ProcessState p m @-}
{-@ reflect priorState @-}
priorState :: ProcessState p m -> ProcessState p m
priorState (_e:es) = es

{-@ statePriorTo :: s:ProcessState p m -> {e:Event p m | listElem e s} -> ProcessState p m @-}
{-@ reflect statePriorTo @-}
statePriorTo :: (Eq p, Eq m) => ProcessState p m -> Event p m -> ProcessState p m
statePriorTo s e = tailAfter e s


-- * Execution type

-- | An execution contains @xProcesses@, a mapping of process-ID to
-- process-state, and @xEventOrder@ a relation for which the transitive closure
-- is the happens-before relation.
data Execution p m = Execution
    { xProcesses :: Assoc p (ProcessState p m)
    , xEventOrder :: BinaryRelation (Event p m) (Event p m)
    }
{-@
data Execution p m = Execution
    { xProcesses :: Assoc p (ProcessState p m)
    , xEventOrder :: BinaryRelation (Event p m) (Event p m)
    }
@-} -- To create measures for each field.

-- | The first/empty execution.
{-@ reflect execution0 @-}
execution0 :: Execution p m
execution0 = Execution assocEmpty brEmpty


-- ** Values derived from an execution

-- | The sequence of events which have taken place on the process (or the empty
-- sequence).
{-@ reflect xProcessState @-}
xProcessState :: Eq p => Execution p m -> p -> ProcessState p m
xProcessState x p = case assocLookup (xProcesses x) p of
    Just s -> s
    Nothing -> []

-- | The set of all events in all process-states in an execution.
{-@ reflect xEvents @-}
xEvents :: (Ord p, Ord m) => Execution p m -> Set (Event p m)
xEvents x
    = listFoldr setUnion setEmpty -- fold the sets into one
    ( listMap setFromList -- convert the process-states to sets
    ( listMap tupleSecond -- get all the process-states
    ( xProcesses x
    )))

-- | The happens-before relation (transitive closure of the event-order relation).
{-@ reflect happensBeforeRelation @-}
happensBeforeRelation :: (Ord p, Ord m) => Execution p m -> BinaryRelation (Event p m) (Event p m)
happensBeforeRelation x = brTransitive (xEventOrder x)

-- | Does the pair @(e1, e2)@ appear in the happens-before relation?
{-@ reflect happensBefore @-}
happensBefore :: (Ord p, Ord m) => Execution p m -> Event p m -> Event p m -> Bool
happensBefore x e1 e2 = setMember (e1, e2) (happensBeforeRelation x)

-- | Does event @e1@ come before @e2@ on process @p@ in the execution?
--
-- This is Gomes' notion of comes-before: "e1 \sqrsubset^i e2 <=> \exists xs,
-- ys, and zs s.t. xs@[e1]@ys@[e2]@zs = history i". Except our process-states
-- are reversed (newer events are cons'd to the left; tail is prior state).
-- Therefore, we say e1 comes-before e2 when e1 is in the tail after (prior
-- state of) e2.
{-@ reflect comesBefore @-}
{-@ comesBefore :: x:Execution p m -> Event p m -> Event p m -> {i:p | assocKey (xProcesses x) i} -> Bool @-}
comesBefore :: (Eq p, Eq m) => Execution p m -> Event p m -> Event p m -> p -> Bool
comesBefore x e1 e2 p =
    let history = assocKeyLookup (xProcesses x) p
    in if listElem e2 history then listElem e1 (statePriorTo history e2) else False

-- | Does the pair @(e1, e2)@ appear in the process-order relation? This is not
-- implemented by tracking a process relation, but by checking whether @e1@
-- comes before @e2@ on any process in the execution.
-- {-@ reflect processOrder @-}
processOrder :: (Eq p, Eq m) => Execution p m -> Event p m -> Event p m -> Bool
processOrder x e1 e2
    = listOrMap (comesBefore x e1 e2)
    ( assocKeys
    ( xProcesses x
    ))
