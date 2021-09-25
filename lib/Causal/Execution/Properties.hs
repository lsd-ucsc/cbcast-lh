{-# OPTIONS_GHC "-Wno-unused-imports" #-} -- LH needs the qualified imports for SMT things
module Causal.Execution.Properties where
-- Properties of reachable executions.

import Language.Haskell.Liquid.ProofCombinators

import Redefined.Proof
import Redefined.Function
import Redefined.Bool
import Redefined.Tuple
import Redefined.List
import qualified Redefined.Set

import qualified Data.Assoc
import qualified Data.BinaryRelation

import Causal.Execution.Type
import Causal.Execution.Semantics
import Causal.Execution.Reachable


-- * General properties

{-@
listIsTailOfTransitivity
    ::   c : [a]
    -> { b : [a] | listIsTailOf c b }
    -> { a : [a] | listIsTailOf b a }
    -> { listIsTailOf c a }
@-}
listIsTailOfTransitivity :: Eq a => [a] -> [a] -> [a] -> Proof
listIsTailOfTransitivity _c _b _a = () *** Admit

{-@
everInStateImpliesEverInTailState
    ::  vr : ValidRules p m
    ->   p : p
    -> { s : ProcessState p m | xProcessEverInState (applyValidRules vr) p s && s /= []}
    -> { xProcessEverInState (applyValidRules vr) p (tail s) }
@-}
everInStateImpliesEverInTailState :: (Ord p, Ord m) => [Rule p m] -> p -> ProcessState p m -> Proof
everInStateImpliesEverInTailState vr p (e:es)
    | xProcessHasState x p (e:es) -- case of xProcessEverInState
        =   xProcessState x p == (e:es) -- definition of xProcessHasState
        === es `listIsTailOf` xProcessState x p -- definition of xProcessHasPriorState
        === xProcessHasPriorState x p es -- case of xProcessEverInState
        === xProcessEverInState x p es -- conclusion
        *** QED
    | xProcessHasPriorState x p (e:es) -- case of xProcessEverInState
        =   (e:es) `listIsTailOf` xProcessState x p -- definition of xProcessHasPriorState
        === es `listIsTailOf` (e:es)
            ? listIsTailOfTransitivity es (e:es) (xProcessState x p)
        === es `listIsTailOf` xProcessState x p -- definition of xProcessHasPriorState
        === xProcessHasPriorState x p es -- case of xProcessEverInState
        === xProcessEverInState x p es -- conclusion
        *** QED
    | otherwise
        = () ? xProcessEverInState x p (e:es) -- premise failed
  where
    x = applyValidRules vr

-- | If the process state @s1@ prior to event @e@ is process state @s0@, then
-- @s0@ is a tail-sublist of @s1@.
{-@ ple statePriorToIsTailOfState @-}
{-@
statePriorToIsTailOfState
    ::  s1 : ProcessState p m
    ->   e : Event p m
    -> {s0 : ProcessState p m | statePriorTo s1 e == Just s0 }
    -> { listIsTailOf s0 s1 }
@-}
statePriorToIsTailOfState :: (Eq p, Eq m) => ProcessState p m -> Event p m -> ProcessState p m -> Proof
statePriorToIsTailOfState [] e s0
        = statePriorTo [] e === Nothing === Just s0
        *** QED -- case is impossible
statePriorToIsTailOfState (e1:es) e s0
    | e1 == e
        =   statePriorTo (e1:es) e
        === Just es -- by defn of statePriorTo
        === Just s0 -- by premises
        *** QED
    | otherwise
        =   statePriorToIsTailOfState es e s0

-- | If a process has a state @s@ prior to an event @e@, then that process was
-- at some point in state @s@.
{-@ ple statePriorToImpliesEverInState @-}
{-@
statePriorToImpliesEverInState
    ::  vr : ValidRules p m
    ->   p : p
    ->   e : Event p m
    -> { s : ProcessState p m | xProcessHasStatePriorToEvent (applyValidRules vr) p s e }
    -> { xProcessEverInState (applyValidRules vr) p s }
@-}
statePriorToImpliesEverInState :: (Ord p, Ord m) => [Rule p m] -> p -> Event p m -> ProcessState p m -> Proof
statePriorToImpliesEverInState vr p e s
--  =   xProcessHasStatePriorToEvent x p s e
--  === statePriorTo (xProcessState x p) e == Just s
--      ? statePriorToIsTailOfState (xProcessState x p) e s
--  === s `listIsTailOf` xProcessState x p
--  === xProcessHasPriorState x p s
--  === xProcessEverInState x p s
--  *** QED
    = statePriorToIsTailOfState (xProcessState x p) e s
  where
    x = applyValidRules vr

{-@ reflect eventHasMessage @-}
eventHasMessage :: Eq m => Event p m -> m -> Bool
eventHasMessage (Deliver _ep em) m = em == m
eventHasMessage (Broadcast em) m = em == m

{-@ reflect eventIsDeliver @-}
eventIsDeliver :: Event p m -> Bool
eventIsDeliver Deliver{} = True
eventIsDeliver Broadcast{} = False

{-@ reflect eventIsDeliverAtProcess @-}
eventIsDeliverAtProcess :: Eq p => Event p m -> p -> Bool
eventIsDeliverAtProcess (Deliver ep _em) p = ep == p
eventIsDeliverAtProcess (Broadcast _em) _p = False

{-@ reflect eventIsDeliverAtProcessOrNotDeliver @-}
eventIsDeliverAtProcessOrNotDeliver :: Eq p => Event p m -> p -> Bool
eventIsDeliverAtProcessOrNotDeliver (Deliver ep _em) p = ep == p
eventIsDeliverAtProcessOrNotDeliver (Broadcast _em) _p = True

{-@ reflect processStateEventsAtProcess @-}
processStateEventsAtProcess :: Eq p => ProcessState p m -> p -> Bool
processStateEventsAtProcess s p =
    listAndMap (funFlip eventIsDeliverAtProcessOrNotDeliver p) s

{-@ reflect xProcessStatesOwned @-}
xProcessStatesOwned :: Eq p => Execution p m -> Bool
xProcessStatesOwned x = listAndMap xProcessStatesOwnedHelper (xProcesses x)
{-@ reflect xProcessStatesOwnedHelper @-}
xProcessStatesOwnedHelper :: Eq p => (p, ProcessState p m) -> Bool
xProcessStatesOwnedHelper (p, s) = processStateEventsAtProcess s p

{-@ ple semanticsPreservesProcessStatesOwned @-}
{-@
semanticsPreservesProcessStatesOwned
    ::   r : Rule p m
    -> { s : Execution p m | premisesHold r s && xProcessStatesOwned s }
    -> { xProcessStatesOwned (semantics r s) }
@-}
semanticsPreservesProcessStatesOwned :: Rule p m -> Execution p m -> Proof
semanticsPreservesProcessStatesOwned (BroadcastRule rp rm) x
    =   ()
    *** Admit
semanticsPreservesProcessStatesOwned (DeliverRule rp rm) x
    =   ()
    *** Admit

{-@ ple definitionOfDeliverEvent @-}
{-@
definitionOfDeliverEvent
    ::   e : Event p m
    -> { p : p | eventIsDeliverAtProcess e p }
    -> { m : m | eventHasMessage e m }
    -> { e == Deliver p m }
@-}
definitionOfDeliverEvent :: Event p m -> p -> m -> Proof
definitionOfDeliverEvent Broadcast{} p m = ()
definitionOfDeliverEvent Deliver{} p m = ()

-- | If a process @p@ was ever in state @s@ and event @e@ is in @s@, then the
-- event is in in that process' state.
{-@
processHasEventsInPriorStates
    ::  vr : ValidRules p m
    ->   p : p
    -> { s : ProcessState p m | xProcessEverInState (applyValidRules vr) p s }
    -> { e : Event p m | listElem e s }
    -> { xProcessHasEvent (applyValidRules vr) p e }
@-}
processHasEventsInPriorStates :: [Rule p m] -> p -> ProcessState p m -> Event p m -> Proof
processHasEventsInPriorStates _vr _p _s _e = () *** Admit

-- | If an event @e@ occured on a process @p@ in an execution then the process
-- in the event is @p@.
{-@ ple eventsOnProcessOwned @-}
{-@
eventsOnProcessOwned
    ::  vr : ValidRules p m
    ->   p : p
    -> { e : Event p m | xProcessHasEvent (applyValidRules vr) p e }
    -> { eventIsDeliverAtProcessOrNotDeliver e p }
@-}
eventsOnProcessOwned :: (Ord p, Ord m) => [Rule p m] -> p -> Event p m -> Proof
eventsOnProcessOwned vr p e =
    case vr of
        [] -> () -- premise doesn't hold
        r:rs -> () *** Admit
  where
    x = applyValidRules vr

-- | If a process @p@ was ever in a state @s@ and message @m@ was delivered at
-- that process state, then an event @Deliver p m@ exists in @s@.
{-@ ple stateDeliveredImpliesListElem @-}
{-@
stateDeliveredImpliesListElem
    ::  vr : ValidRules p m
    ->   p : p
    -> { s : ProcessState p m | xProcessEverInState (applyValidRules vr) p s }
    -> { m : m | stateDelivered s m }
    -> { listElem (Deliver p m) s }
@-}
stateDeliveredImpliesListElem :: (Ord p, Ord m) => [Rule p m] -> p -> ProcessState p m -> m -> Proof
stateDeliveredImpliesListElem _vr _p [] _m = () -- premises don't hold
stateDeliveredImpliesListElem vr p (e:es) m
--  =   (stateDelivered (e:es) m
--  === listOrMap (eventDeliversMessage m) (e:es)
--  === listOr (listMap (eventDeliversMessage m) (e:es))
--  === listFoldr boolOr False (listMap (eventDeliversMessage m) (e:es))
--  === listFoldr boolOr False (eventDeliversMessage m e:(listMap (eventDeliversMessage m) es))
--  === boolOr (eventDeliversMessage m e) (listFoldr boolOr False (listMap (eventDeliversMessage m) es))
--  === boolOr (eventDeliversMessage m e) (stateDelivered es m)
    | stateDelivered es m
        = ()
            ? everInStateImpliesEverInTailState vr p (e:es)
            ? stateDeliveredImpliesListElem vr p es m
    | eventDeliversMessage m e
        = eventDeliversMessage m e
            ? processHasEventsInPriorStates vr p (e:es) e
            ? eventsOnProcessOwned vr p e
        === eventIsDeliverAtProcess e p
            ? definitionOfDeliverEvent e p m
        === (e == Deliver p m)
        === listElem (Deliver p m) (e:es)
        *** QED
  where
    x = applyValidRules vr


-- * Correctness properties

-- | An event in one process-state does not appear in another process-state.
{-@
eventsBelongToOneProcess
    ::  vr : ValidRules p m
    ->   e : Event p m
    -> { i : p | xProcessHasEvent (applyValidRules vr) i e }
    -> { j : p | i /= j }
    -> { not (xProcessHasEvent (applyValidRules vr) j e) }
@-}
eventsBelongToOneProcess :: [Rule p m] -> Event p m -> p -> p -> Proof
eventsBelongToOneProcess _rules _e _i _j = () *** Admit

-- XXX what about properties for the eventOrder or happensBefore relation?


-- * Gomes properties


-- ** Node-histories properties

-- | All heads in the list do not appear in their tail.
{-@ reflect listElementsDistinct @-}
listElementsDistinct :: Eq a => [a] -> Bool
listElementsDistinct [] = True
listElementsDistinct (x:xs) = not (listElem x xs) && listElementsDistinct xs

-- | Gomes' histories-distinct property on the node-histories locale.
{-@
historiesDistinct
    ::  vr : ValidRules p m
    ->   i : p
    -> { listElementsDistinct (xProcessState (applyValidRules vr) i) }
@-}
historiesDistinct :: [Rule p m] -> p -> Proof
historiesDistinct _rules _p = () *** Admit


-- ** Network properties

-- | Gomes' delivery-has-a-cause property on the network locale.
--
--      [[ Deliver m \in set (history i) ]] \implies \exists j. Broadcast m \in set (history j)
{-@
deliveryHasACause
    ::  vr : ValidRules p m
    ->   m : m
    -> { i : p | xProcessHasEvent (applyValidRules vr) i (Deliver i m) }
    -> {js : ProcessState p m | listElem (Broadcast m) js }
    -> { xHasState (applyValidRules vr) js }
@-}
deliveryHasACause :: [Rule p m] -> m -> p -> ProcessState p m -> Proof
deliveryHasACause _rules _m _i _js = () *** Admit
-- FIXME should we use xProcessHasEvent here or listElem? (this is only a style question)
-- XXX not sure this signature actualy says "there exists j such that .."

-- | Gomes' deliver-locally property on the network locale.
--
--      [[ Broadcast m \in set (history i) ]] \implies Broadcast m \sqrsubset^i Deliver m
{-@
deliverLocally
    ::  vr : ValidRules p m
    ->   m : m
    -> { i : p | xProcessHasEvent (applyValidRules vr) i (Broadcast m) }
    -> { xComesBefore (applyValidRules vr) (Broadcast m) (Deliver i m) i }
@-}
deliverLocally :: [Rule p m] -> m -> p -> Proof
deliverLocally _rules _m _i = () *** Admit

-- | Gomes' msg-id-unique property on the network locale.
--
--      [[ Broadcast m1 \in set (history i);
--         Broadcast m2 \in set (history j);
--         msg-id m1 = msg-id m2 ]] \implies i = j \land m1 = m2
{-@
msgIdUnique
    ::  vr : ValidRules p m
    ->  m1 : m
    -> {m2 : m | m1 == m2 }
    -> { i : p | xProcessHasEvent (applyValidRules vr) i (Broadcast m1) }
    -> { j : p | xProcessHasEvent (applyValidRules vr) j (Broadcast m2) }
    -> { i == j }
@-}
msgIdUnique :: [Rule p m] -> m -> m -> p -> p -> Proof
msgIdUnique _rules _m1 _m2 _i _j = () *** Admit
