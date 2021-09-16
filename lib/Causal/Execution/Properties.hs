{-# OPTIONS_GHC "-Wno-unused-imports" #-} -- LH needs the qualified imports for SMT things
module Causal.Execution.Properties where
-- Properties of reachable executions.

import Language.Haskell.Liquid.ProofCombinators

import Redefined.Proof
import qualified Redefined.Bool
import Redefined.Tuple
import Redefined.List
import qualified Redefined.Set

import qualified Data.Assoc
import qualified Data.BinaryRelation

import Causal.Execution.Type
import Causal.Execution.Semantics
import Causal.Execution.Reachable


-- * General properties

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
