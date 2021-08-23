{-# LANGUAGE GADTs #-}
{-# LANGUAGE NamedFieldPuns #-}
module Causal.ArithmeticSemanticsFun where

data Peano = Z | S Peano
    deriving Eq

type State = Peano

data Rule
    = Add1{p::Peano}
    | AddZ

-- | For each rule, express whether its premises are satisfied in a given
-- state.
{-@ reflect premisesHold @-}
premisesHold :: Rule -> State -> Bool
premisesHold AddZ    Z  = True
premisesHold Add1{p} p' = p == p'
premisesHold _       _  = False

-- Either rule applies to State==Z. The semantics is nondeterministic.
--
-- This is a relation State X State, but the Rule is kind of messing it up.
--
{-@ add1Semantics :: r:Rule -> {s:State | premisesHold r s} -> State @-}
add1Semantics :: Rule -> State -> State
add1Semantics AddZ    Z  = S Z
add1Semantics Add1{p} _p = S p
add1Semantics _       _  = undefined -- LH requires this, even though the premisesHold function *should* rule out other calling conventions.

-- data TRC where
--     Lift :: Rule -> TRC
-- 
-- 
-- add1trc :: TRC -> State -> State
