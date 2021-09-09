module Experiments.GenericSemantics where

{-

type S

relation S ==> S

        premises
[rule]------------
       conclusion

For @s, s' : S@ a conclusion has the form:
    s ==> 's

relation S ==>* S

-}

-- | Semantics state type.
data S = S | E

-- | Summary of all the transition rules for a nondeterministic semantics.
-- Result is a finite list of all the states which can be reached after any one
-- rule from the semantics is applied.
--
-- The implementation of this function could be completed with a rule type `R`,
-- a function to generate possible rule applications `S -> [R]`, and a function
-- `S -> S -> S` to step forward with a rule application.
--
{-@ reflect stateTransition @-}
stateTransition :: S -> [S]
stateTransition = (:[])

-- | The `S ==> S` type which contains all the state transition pairs permitted
-- under this semantics.
--
{-@
type TransitionRelation = (S, S)<{\a b -> listElem b (stateTransition a)}>
@-}

-- | Transitive reflexive closure over stateTransition. Result is an infinite
-- list reflecting successively more rule applications.
{-@ reflect stateTransitionTRC @-}
stateTransitionTRC :: S -> [S]
stateTransitionTRC = (:[])

-- | The `S ==>* S` type
{-@
type TransitionRelationTRC = (S, S)<{\a b -> listElem b (stateTransitionTRC a)}>
@-}

-- {-@ refl :: S -> TransitionRelationTRC @-}
-- refl :: S -> (S, S)
-- refl s = (s, s)

-- | Initial state
{-@ reflect s0 @-}
s0 :: S
s0 = S

{-@
type Reachable X = {tup:TransitionRelationTRC | fst tup == s0 && snd tup == X}
@-}

-- {-@ s0_reachable :: Reachable {s0} @-}
-- s0_reachable :: (S, S)
-- s0_reachable = (s0, s0)
