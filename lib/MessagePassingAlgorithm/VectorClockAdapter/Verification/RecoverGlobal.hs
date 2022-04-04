{-# OPTIONS_GHC "-Wno-unused-imports" #-} -- LH needs bodies of reflected definitions

module MessagePassingAlgorithm.VectorClockAdapter.Verification.RecoverGlobal where

import Language.Haskell.Liquid.ProofCombinators

import Redefined
import VectorClock

import MessagePassingAlgorithm
import MessagePassingAlgorithm.VectorClockAdapter
import MessagePassingAlgorithm.VectorClockAdapter.Verification.ProcessLocalCausalDelivery

-- | Kinda cheating with a function b/c all PIDs are in domain? Might fix that
-- by length indexing it... Or that might not be enough. Probably best to use
-- an assoc.
type Execution mm r = PID -> ProcessHistory mm r

-- | POSTULATE
happensBefore :: Execution mm r -> Event mm r -> Event mm r -> Bool
happensBefore _x _e₁ _e₂ = False
{-@ reflect happensBefore @-}

{-@
type CausalDelivery mm r X PID
    =  {m1 : Message mm r | listElem (Deliver PID m1) (X PID) }
    -> {m2 : Message mm r | listElem (Deliver PID m2) (X PID)
                         && happensBefore X (Broadcast m1) (Broadcast m2) }
    -> {_  : Proof | processOrder (X PID) (Deliver PID m1) (Deliver PID m2)}
@-}

xEmpty :: Execution mm r
xEmpty _p_id = []
{-@ reflect xEmpty @-}

{-@
xEmptyCD
    :: p_id : PID
    -> CausalDelivery mm x {xEmpty} {p_id}
@-}
xEmptyCD :: (Eq mm, Eq r) => PID -> Message mm r -> Message mm r -> Proof
xEmptyCD p_id m₁ _m₂ =
    let e₁ = Deliver p_id m₁ in
        listElem e₁ (xEmpty p_id)
    === listElem e₁ [] -- premise failed
    *** QED

{-@
local2global
    ::     x : Execution VCMM r
    ->  p_id : PID
    ->  ProcessLocalCausalDelivery r {p_id} {x p_id}
    ->  CausalDelivery VCMM r {x} {p_id}
@-}
local2global :: Execution VCMM r -> PID -> (M r -> M r -> Proof) -> M r -> M r -> Proof
local2global x p_id pPLCD m₁ m₂ =
    -- pPLCD m₁ m₂ -- OOPS currently proving false, probably b/c body of happensBefore is False
    () *** Admit

-- Need axiom
--   :: happensBefore X (Broadcast m1) (Broadcast m2)
--   -> vcLess (mVC m1) (mVC m2)

---- -- | Same as our normal definition for PLCD, except this one takes the VC size.
---- {-@
---- type ProcessLocalCausalDeliveryN r N PID PHIST
----     =  {m1 : Msized r {n}   | listElem (Deliver PID m1) PHIST }
----     -> {m2 : Msized r {n}   | listElem (Deliver PID m2) PHIST
----                            && vcLess (mVC m1) (mVC m2) }
----     -> {_ : Proof | processOrder PHIST (Deliver PID m1) (Deliver PID m2) }
---- @-}
---- 
---- {-@
---- local2global
----     ::     n : Nat
----     ->     x : Execution (VCMMsized {n}) r
----     ->  p_id : PIDsized {n}
----     ->  ProcessLocalCausalDeliveryN r {n} {p_id} {x p_id}
----     ->  CausalDelivery (VCMMsized {n}) r {x} {p_id}
---- @-}
---- local2global :: Int -> Execution VCMM r -> PID -> (M r -> M r -> Proof) -> M r -> M r -> Proof
---- local2global n x p_id pPLCD m₁ m₂ =
----     pPLCD (coerce m₁) (coerce m₂)
---- {-@ ple local2global @-}
