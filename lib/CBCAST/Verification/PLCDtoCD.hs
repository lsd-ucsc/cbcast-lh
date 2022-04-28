{-# OPTIONS_GHC "-Wno-unused-imports" #-} -- LH needs bodies of reflected definitions
{-# OPTIONS_GHC "-Wno-warnings-deprecations" #-} -- Hide the "verification only" and "internal use" warnings

module CBCAST.Verification.PLCDtoCD {-# WARNING "Verification only" #-} where

import Language.Haskell.Liquid.ProofCombinators -- (Proof, (===), (***), QED(..), (?))
import Language.Haskell.Liquid.ProofCombinatorsExtra (proofConst)

import Redefined
import VectorClock
import CBCAST.Core
import CBCAST.Verification.ProcessOrder
import CBCAST.Verification.PLCD

-- | An execution is a mapping from process identifier to CBCAST process. The
-- mapping is constrained to only those processes /in/ the execution by the
-- size parameter, @N@.
type Execution r = PID -> Process r
{-@ type Xsized r N = p_id:PIDsized {N} -> {p:Psized r {N} | p_id == pID p} @-}

-- | Happens-before is a binary relation on two events in an execution.
{-@
measure happensBefore :: n:Nat -> Xsized r {n} -> Esized r {n} -> Esized r {n} -> Bool
@-}

-- QQQ: Do we need to say that the events are "in the execution"? 

-- | Causal delivery is defined for an execution, ranging over process
-- identifiers and messages (with constraints).
{-@
type CausalDelivery r N X
    = p_id : PIDsized {N}
    -> {m1 : Msized r {N} | listElem (Deliver p_id m1) (pHist (X p_id)) }
    -> {m2 : Msized r {N} | listElem (Deliver p_id m2) (pHist (X p_id))
                && happensBefore N X (Broadcast m1) (Broadcast m2) }
    -> {_  : Proof | processOrder (pHist (X p_id)) (Deliver p_id m1) (Deliver p_id m2)}
@-}

-- | The empty, initial, execution, x₀, compatible with processes of size @n@.
{-@
xEmpty :: n:Nat -> Xsized r {n} @-}
xEmpty :: Int -> Execution r
xEmpty n p_id = pEmpty n p_id
    `proofConst` pEmptyGivenPID n p_id
{-@ reflect xEmpty @-}

{-@
pEmptyGivenPID :: n:Nat -> p_id:PIDsized {n} -> { p_id == pID (pEmpty n p_id) } @-}
pEmptyGivenPID :: Int -> PID -> Proof
pEmptyGivenPID _n _p_id = ()
{-@ ple pEmptyGivenPID @-} -- I don't feel like copying the body here.

-- | Trivial lemma for xEmptyCD.
{-@
pEmptyHistEmpty :: n:Nat -> p_id:PIDsized {n} -> { [] == pHist (pEmpty n p_id) } @-}
pEmptyHistEmpty :: Int -> PID -> Proof
pEmptyHistEmpty n p_id = () ? pEmpty n p_id
{-@ ple pEmptyHistEmpty @-} -- I don't feel like copying the body here.

-- | The empty execution vacuously observes causal delivery.
{-@
xEmptyCD :: n:Nat -> CausalDelivery r {n} {xEmpty n} @-}
xEmptyCD :: Eq r => Int -> PID -> Message r -> Message r -> Proof
xEmptyCD n p_id m₁ _m₂ =
    let e₁ = Deliver p_id m₁ in
        True
    === listElem e₁ (pHist (xEmpty n p_id))
    === listElem e₁ (pHist (pEmpty n p_id))
        ? pEmptyHistEmpty n p_id
    === listElem e₁ []
    *** QED

{-@
vcLessImpliesHb
    ::   n : Nat
    ->   x : Xsized r {n}
    ->  m1 : Msized r {n}
    ->{ m2 : Msized r {n} | vcLess (mVC m1) (mVC m2) }
    -> { happensBefore n x (Broadcast m1) (Broadcast m2) }
@-}
vcLessImpliesHb :: Int -> Execution r -> Message r -> Message r -> Proof
vcLessImpliesHb _n _x _m₁ _m₂ = () *** Admit

{-@
hbImpliesVcLess
    ::   n : Nat
    ->   x : Xsized r {n}
    ->  m1 : Msized r {n}
    ->{ m2 : Msized r {n} | happensBefore n x (Broadcast m1) (Broadcast m2) }
    -> { vcLess (mVC m1) (mVC m2) }
@-}
hbImpliesVcLess :: Int -> Execution r -> Message r -> Message r -> Proof
hbImpliesVcLess _n _x _m₁ _m₂ = () *** Admit

{-@
plcdToCD
    :: n : Nat
    -> x : Xsized r {n}
    -> ( p_id:PIDsized {n} -> PLCD r {n} {x p_id} )
    -> CausalDelivery r {n} {x}
@-}
plcdToCD :: Int -> Execution r -> (PID -> (Message r -> Message r -> Proof))
                                   -> (PID ->  Message r -> Message r -> Proof )
plcdToCD n x xPLCD p_id m₁ m₂ =
    ()  ? (p_id === pID (x p_id))
        ? hbImpliesVcLess n x m₁ m₂
        ? xPLCD p_id m₁ m₂
