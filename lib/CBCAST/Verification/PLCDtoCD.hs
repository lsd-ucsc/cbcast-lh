{-# OPTIONS_GHC "-Wno-unused-imports" #-} -- LH needs bodies of reflected definitions
{-# OPTIONS_GHC "-Wno-warnings-deprecations" #-} -- Hide the "verification only" and "internal use" warnings

module CBCAST.Verification.PLCDtoCD {-# WARNING "Verification only" #-} where

import Language.Haskell.Liquid.ProofCombinators (Proof, (===), (***), QED(..))

import Redefined
import CBCAST.Core
import CBCAST.Verification.ProcessOrder

-- | An execution is a mapping from process identifier to process history. The
-- mapping is constrained to only those processes /in/ the execution by the
-- size parameter, @N@.
type Execution r = PID -> ProcessHistory r
{-@ type Xsized r N = PIDsized {N} -> Hsized r {N} @-}

-- | Happens-before is a binary relation on two events in an execution.
--
-- QQQ: Do we need to say that the events are "in the execution"? 
{-@
measure happensBefore :: n:Nat -> Xsized r {n} -> Esized r {n} -> Esized r {n} -> Bool
@-}

-- | Causal delivery is defined for an execution, ranging over process
-- identifiers and messages (with constraints).
{-@
type CausalDelivery r N X
    =  pid : PIDsized {N}
    -> {m1 : Msized r {N} | listElem (Deliver pid m1) (X pid) }
    -> {m2 : Msized r {N} | listElem (Deliver pid m2) (X pid)
                && happensBefore N X (Broadcast m1) (Broadcast m2) }
    -> {_  : Proof | processOrder (X pid) (Deliver pid m1) (Deliver pid m2)}
@-}

-- | The empty, initial, execution, x₀, compatible with processes of size @n@.
{-@
xEmpty :: n:Nat -> Xsized r {n} @-}
xEmpty :: Int -> Execution r
xEmpty _n _pid = []
{-@ reflect xEmpty @-}

{-@
xEmptyCD :: n:Nat -> CausalDelivery r {n} {xEmpty n} @-}
xEmptyCD :: Eq r => Int -> PID -> Message r -> Message r -> Proof
xEmptyCD n pid m₁ m₂ =
    let e₁ = Deliver pid m₁ in
        listElem e₁ (xEmpty n pid)
    === listElem e₁ [] -- premise failed
    *** QED
