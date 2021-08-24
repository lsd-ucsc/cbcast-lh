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

{-@
implSimulatesSpecVerbose

    ::   implAction : Impl.Rule
    ->   implState0 : Impl.State
    -> { implState1 : Impl.State | implState1 == Impl.causalDeliverySemantics implState0 implAction }

    -> { specAction : Spec.Rule  | specAction == convertAction implAction }
    -> { specState0 : Spec.State | specState0 == convertState implState0 }
    -> { specState1 : Spec.State | specState1 == Spec.causalDeliverySemantics specState0 specAction }

    -> { specState1 == convertState implState1 }
@-}
implSimulatesSpecVerbose
    :: Impl.Rule -> Impl.State -> Impl.State
    -> Spec.Rule -> Spec.State -> Spec.State
    -> Proof
implSimulatesSpecVerbose _ _ _ _ _ _ = () *** Admit

-- TODO: write it down again, but generate all the parts which are derived

-- FIXME: make sure to state somewhere:
--
-- Impl.premisesHold implState0 implAction
-- Spec.premisesHold specState0 specAction
--
-- And this probably requires a proof about the premises holding THROUGH the conversion functions...
