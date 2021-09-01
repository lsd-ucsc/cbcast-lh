{-# OPTIONS_GHC "-Wno-unused-imports" #-} -- LH needs BinaryRelation to be imported for specs
{-# LANGUAGE NamedFieldPuns #-}
module Causal.CDSDsimulatesCDS where

import Redefined
import qualified BinaryRelation -- Required to fix LH "free vars" error
import Language.Haskell.Liquid.ProofCombinators

import qualified Causal.CausalDeliverySemantics as Spec
import qualified Causal.CausalDeliverySemanticsDummy as Impl

{-@ reflect convertProcess @-}
convertProcess :: Impl.Process -> Spec.Process
convertProcess (Impl.Process n) = Spec.Process n

{-@ reflect convertMessage @-}
convertMessage :: Impl.Message -> Spec.Message
convertMessage (Impl.Message n) = Spec.Message n

{-@ reflect convertState @-}
convertState :: Impl.State -> Spec.State
convertState Impl.State{{-Impl.delivered,Impl.requires-}} = Spec.State
    { Spec.delivered = setEmpty -- delivered
    , Spec.requires = setEmpty -- requires
    }

{-@ reflect convertAction @-}
convertAction :: Impl.Rule -> Spec.Rule
convertAction Impl.Send{Impl.sender,Impl.message}
    = Spec.Send{Spec.sender=convertProcess sender,Spec.message=convertMessage message}
convertAction Impl.Deliver{Impl.p0,Impl.receiver,Impl.message}
    = Spec.Deliver{Spec.p0=convertProcess p0,Spec.receiver=convertProcess receiver,Spec.message=convertMessage message}

{-@ ple convertPreservesApplicability @-}
{-@
convertPreservesApplicability
    ::  s:Impl.State
    -> {r:Impl.Rule | Impl.premisesHold s r}
    -> { Spec.premisesHold (convertState s) (convertAction r) }
@-}
convertPreservesApplicability :: Impl.State -> Impl.Rule -> Proof
convertPreservesApplicability _ _ = () *** Admit

-- |
--
-- Spec_0 ==>* Spec_1 ==>* Spec_2
--   ^           ^           ^
--   |           |           |
-- Impl_0 ==>* Impl_1 ==>* Impl_2
--
{-@ reflect implSimulatesSpecB @-}
{-@ implSimulatesSpecB :: s:Impl.State -> {r:Impl.Rule | Impl.premisesHold s r} -> Bool @-}
implSimulatesSpecB :: Impl.State -> Impl.Rule -> Bool
implSimulatesSpecB implState0 implAction =
    let
        implState1 = Impl.causalDeliverySemantics implState0 implAction
        -- Now simulate that in the spec.
        specState0 = convertState implState0 `proofConst` convertPreservesApplicability implState0 implAction
        specAction = convertAction implAction
        specState1 = Spec.causalDeliverySemantics specState0 specAction
    in
        -- Finally, assert that the two semantics arrive at the same state in the spec.
        specState1 == convertState implState1
        -- Gan: define a different notion of equality than `==` (intensional)
        -- because `==` (intensional) is hard and unnecessary

{-@
implSimulatesSpec
    :: s:Impl.State
    -> r:Impl.Rule
    -> { implSimulatesSpecB s r }
@-}
implSimulatesSpec :: Impl.State -> Impl.Rule -> Proof
implSimulatesSpec _ _ = () *** Admit
