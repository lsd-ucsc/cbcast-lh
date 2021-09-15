{-# OPTIONS_GHC "-Wno-unused-imports" #-} -- LH needs the qualified imports for SMT things
module Causal.Execution.Type where

import qualified Redefined.Bool
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

-- | What is the state prior to the most recent event?
--
-- XXX function is not used anywhere
{-@ reflect statePrior @-}
statePrior :: ProcessState p m -> Maybe (ProcessState p m)
statePrior (_e:es) = Just es
statePrior [] = Nothing

-- | What is the state prior to the given event?
{-@ reflect statePriorTo @-}
statePriorTo :: (Eq p, Eq m) => ProcessState p m -> Event p m -> Maybe (ProcessState p m)
statePriorTo [] _e = Nothing
statePriorTo (e:es) event
    | e == event = Just es
    | otherwise = statePriorTo es event


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

-- *** Convenience predicates for LH signatures

-- | Does the execution have the process?
{-@ reflect xHasProcess @-}
xHasProcess :: Eq p => Execution p m -> p -> Bool
xHasProcess x p = assocKey (xProcesses x) p

-- | Is the process state in the execution equal to the given process state?
{-@ reflect xProcessHasState @-}
xProcessHasState :: (Eq p, Eq m) => Execution p m -> p -> ProcessState p m -> Bool
xProcessHasState x p s = xProcessState x p == s

xProcessHasEvent :: (Eq p, Eq m) => Execution p m -> p -> Event p m -> Bool
xProcessHasEvent x p e = listElem e (xProcessState x p)

--- *** Ordering relations

-- | Produce the happens-before relation (transitive closure of the event-order
-- relation).
{-@ reflect xHappensBeforeRelation @-}
xHappensBeforeRelation :: (Ord p, Ord m) => Execution p m -> BinaryRelation (Event p m) (Event p m)
xHappensBeforeRelation x = brTransitive (xEventOrder x)

-- | Does the pair @e1 -> e2@ occur in the happens-before relation?
{-@ reflect xHappensBefore @-}
xHappensBefore :: (Ord p, Ord m) => Execution p m -> Event p m -> Event p m -> Bool
xHappensBefore x e1 e2 = setMember (e1, e2) (xHappensBeforeRelation x)

-- | Does event @e1@ come before @e2@ on process @p@ in the execution?
--
-- This is Gomes' notion of comes-before: "e1 \sqrsubset^i e2 <=> \exists xs,
-- ys, and zs s.t. xs@[e1]@ys@[e2]@zs = history i". Except our process-states
-- are reversed (newer events are cons'd to the left; tail is prior state).
-- Therefore, we say e1 comes-before e2 when e1 is in the tail after (prior
-- state of) e2.
{-@ reflect xComesBefore @-}
xComesBefore :: (Eq p, Eq m) => Execution p m -> Event p m -> Event p m -> p -> Bool
xComesBefore x e1 e2 p = case statePriorTo (xProcessState x p) e2 of
    Nothing -> False -- XXX e2 doesn't occur on p
    Just s -> listElem e1 s -- XXX does e1 occur in s, the state prior to e2?

-- | Does event @e1@ come before @e2@ on any process in the execution?
-- {-@ reflect xProcessOrder @-}
xProcessOrder :: (Eq p, Eq m) => Execution p m -> Event p m -> Event p m -> Bool
xProcessOrder x e1 e2
    = listOrMap (xComesBefore x e1 e2)
    ( assocKeys
    ( xProcesses x
    ))
