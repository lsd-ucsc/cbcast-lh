{-# OPTIONS_GHC "-Wno-unused-imports" #-} -- LH needs the qualified imports for SMT things
module Causal.Execution.Properties where
-- Properties of reachable executions.

import Language.Haskell.Liquid.ProofCombinators

import qualified Redefined.Bool
import Redefined.Tuple
import Redefined.List
import qualified Redefined.Set

import qualified Data.Assoc
import qualified Data.BinaryRelation

import Causal.Execution.Type
import Causal.Execution.Semantics
import qualified Causal.Execution.Reachable


-- * Correctness properties

-- | If a process has a state @s@ prior to an event @e@, then that process was
-- at some point in state @s@.
{-@
statePriorToImpliesEverInState
    ::  vr : ValidRules p m
    ->   p : p
    ->   e : Event p m
    -> { s : ProcessState p m | xProcessHasStatePriorToEvent (applyValidRules vr) p s e }
    -> { xProcessEverInState (applyValidRules vr) p s }
@-}
statePriorToImpliesEverInState :: [Rule p m] -> p -> Event p m -> ProcessState p m -> Proof
statePriorToImpliesEverInState _vr _p _e _s = () *** Admit

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
stateDeliveredImpliesListElem :: [Rule p m] -> p -> ProcessState p m -> m -> Proof
stateDeliveredImpliesListElem _vr _p [] _m = ()
stateDeliveredImpliesListElem _vr _p _s _m = () *** Admit

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
