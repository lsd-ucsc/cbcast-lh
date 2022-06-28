{-# OPTIONS_GHC "-Wno-unused-imports" #-} -- LH needs bodies of reflected definitions
{-# OPTIONS_GHC "-Wno-warnings-deprecations" #-} -- Hide the "verification only" and "internal use" warnings

-- | Global definitions and properties relating to causal delivery.
module CBCAST.Verification.CD {-# WARNING "Verification only" #-} where

import Language.Haskell.Liquid.ProofCombinators -- (Proof, (===), (***), QED(..), (?))
import Language.Haskell.Liquid.ProofCombinatorsExtra (proofConst)

import Redefined
import VectorClock
import CBCAST.Core
import CBCAST.Verification.ProcessOrder
import CBCAST.Verification.PLCD




-- * Execution

-- | An execution is a mapping from process identifier to CBCAST processes. The
-- mapping is constrained to only those processes /in/ the execution by the
-- size parameter, @N@.
type Execution r = PID -> Process r
{-@ type Xsized r N = p_id_k:PIDsized {N} -> {p_v:Psized r {N} | p_id_k == pID p_v} @-}
---- QQQ Xsized breaks xSetPidProc b/c of name collisions again. Repro5, issue #2017

-- | The empty, initial, execution, x₀, for processes of size @n@.
{-@
xEmpty :: n:Nat -> Xsized r {n} @-}
xEmpty :: Int -> Execution r
xEmpty n p_id = pEmpty n p_id
    `proofConst` pEmptyGivenPID n p_id
{-@ reflect xEmpty @-}

-- | Update an execution/mapping with a new PID/Process pair.
{-@
xSetPidProc :: n:Nat -> p_id:PIDsized {n} -> {p:Psized r {n} | p_id == pID p} -> Xsized r {n} -> Xsized r {n} @-}
xSetPidProc :: Int -> PID -> Process r -> Execution r -> Execution r
---- QQQ xSetPidProc _n = setMapping -- This should work, per Repro6, so I'm guessing theres another name-collision issue
xSetPidProc _n k v mapping target
    | target == k = v
    | otherwise = mapping target
{-@ reflect xSetPidProc @-}

-- | Update an execution/mapping with a new Process (using its PID).
{-@
xSetProc :: n:Nat -> Psized r {n} -> Xsized r {n} -> Xsized r {n} @-}
xSetProc :: Int -> Process r -> Execution r -> Execution r
xSetProc n p = xSetPidProc n (pID p) p
{-@ reflect xSetProc @-}




-- * HB-VC isomorphism

-- | Happens-before (e → e') is a binary relation on two events in an execution.
{-@
measure happensBefore :: n:Nat -> Xsized r {n} -> Esized r {n} -> Esized r {n} -> Bool
@-}

-- | Vector clocks preserve the happens-before relation.
--
-- e → e' ⇒ VC(e) < VC(e')
{-@
preserveHB
    ::   n : Nat
    ->   x : Xsized r {n}
    ->  m1 : Msized r {n}
    ->{ m2 : Msized r {n} | happensBefore n x (Broadcast m1) (Broadcast m2) }
    -> { vcLess (mVC m1) (mVC m2) }
@-}
preserveHB :: Int -> Execution r -> Message r -> Message r -> Proof
preserveHB _n _x _m₁ _m₂ = () *** Admit -- Taken as an axiom for now.

-- | Vector clocks reflect the happens-before relation.
--
-- VC(e) < VC(e') ⇒ e → e'
{-@
reflectHB
    ::   n : Nat
    ->   x : Xsized r {n}
    ->  m1 : Msized r {n}
    ->{ m2 : Msized r {n} | vcLess (mVC m1) (mVC m2) }
    -> { happensBefore n x (Broadcast m1) (Broadcast m2) }
@-}
reflectHB :: Int -> Execution r -> Message r -> Message r -> Proof
reflectHB _n _x _m₁ _m₂ = () *** Admit -- Taken as an axiom for now.




-- * Causal delivery

-- | Causal delivery is defined for an execution, ranging over process
-- identifiers and messages. This is close to the literature's definition.
{-@
type CausalDelivery r N X
    = p_id : PIDsized {N}
    -> {m1 : Msized r {N} | listElem (Deliver p_id m1) (pHist (X p_id)) }
    -> {m2 : Msized r {N} | listElem (Deliver p_id m2) (pHist (X p_id))
                && happensBefore N X (Broadcast m1) (Broadcast m2) }
    -> {_  : Proof | processOrder (pHist (X p_id)) (Deliver p_id m1) (Deliver p_id m2)}
@-}

-- | If all processes in an execution are PLCD, then the execution is CD.
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
        ? preserveHB n x m₁ m₂
        ? xPLCD p_id m₁ m₂

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




-- * Alternate Causal delivery

-- | Alternate CD definition which excludes an unsatisfying execution
-- identified by Gan and Simon and others, but which is permitted by the more
-- tradition definition of CD above.
-- <https://ucsc-lsdlab.zulipchat.com/#narrow/stream/296459-casl/topic/cbcast.20paper.3A.20cbcast.3D.3Ecd.3F.3F/near/280539835>
--
-- a --+----+-->
--   m₁|  m₂|
--     *    |
--          v
-- b -------+-->
--
-- This execution does not meet the premises of CausalDelivery, and so it is
-- vacuously satisfied. CausalDeliveryAlternate doesn't permit this execution.
--
-- @
-- CausalDeliveryAlternate : Execution → PID → Set
-- CausalDeliveryAlternate x pid
--   = ∀ (m₁ m₂ : Message)
--   → Deliver pid m₂ ∈ x pid
--   → HappensBefore x (Broadcast m₁) (Broadcast m₂)
--   → (Deliver pid m₁ ∈ x pid) × (ProcessOrder (x pid) (Deliver pid m₁) (Deliver pid m₂))
-- @
{-@
type CausalDeliveryAlternate r N X
    = p_id : PIDsized {N}
    ->  m1 : Msized r {N}
    -> {m2 : Msized r {N} |
            listElem (Deliver p_id m2) (pHist (X p_id))
            && happensBefore N X (Broadcast m1) (Broadcast m2) }
    -> {_  : Proof |
            listElem (Deliver p_id m1) (pHist (X p_id))
            && processOrder (pHist (X p_id)) (Deliver p_id m1) (Deliver p_id m2) }
@-}

-- | If all processes in an execution are PLCD, then the execution is CDA.
{-@
plcdToCDA
    :: n : Nat
    -> x : Xsized r {n}
    -> ( p_id:PIDsized {n} -> PLCD r {n} {x p_id} )
    -> CausalDeliveryAlternate r {n} {x}
@-}
plcdToCDA :: Int -> Execution r -> (PID -> (Message r -> Message r -> Proof))
                                -> (PID ->  Message r -> Message r -> Proof )
plcdToCDA n x xPLCD p_id m₁ m₂ = () *** Admit -- TODO
