module Causal.CDSDsimulatesCDS where

import Redefined
import Language.Haskell.Liquid.ProofCombinators

import qualified Causal.CausalDeliverySemantics as Spec
import qualified Causal.CausalDeliverySemanticsDummy as Impl

{-@ reflect convertState @-}
convertState :: Impl.State -> Spec.State
convertState _ = Spec.State setEmpty setEmpty -- TODO

{-@ reflect convertAction @-}
convertAction :: Impl.Rule -> Spec.Rule
convertAction _ = Spec.Send (Spec.Process 0) (Spec.Message 0) -- TODO

{-@ ple convertPreservesApplicability @-}
{-@
convertPreservesApplicability
    ::  s:Impl.State
    -> {r:Impl.Rule | Impl.premisesHold s r}
    -> { Spec.premisesHold (convertState s) (convertAction r) }
@-}
convertPreservesApplicability :: Impl.State -> Impl.Rule -> Proof
convertPreservesApplicability _ _ = ()

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

{-@
implSimulatesSpec
    :: implState0:Impl.State
    -> implAction:Impl.Rule
    -> { implSimulatesSpecB implState0 implAction }
@-}
implSimulatesSpec :: Impl.State -> Impl.Rule -> Proof
implSimulatesSpec _ _ = () *** Admit
