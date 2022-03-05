{-# OPTIONS_GHC "-Wno-unused-imports" #-} -- LH needs bodies of reflected definitions

-- Process local causal delivery definition for a process history.
module MessagePassingAlgorithm.VectorClockAdapter.Verification.ProcessLocalCausalDelivery where

import Language.Haskell.Liquid.ProofCombinators

import Redefined
import VectorClock
import MessagePassingAlgorithm
import MessagePassingAlgorithm.VectorClockAdapter

import Redefined.Verification

{-@
type ProcessLocalCausalDelivery r PID PHIST
    =  {m1 : Message VCMM r | listElem (Deliver PID m1) PHIST }
    -> {m2 : Message VCMM r | listElem (Deliver PID m2) PHIST
                && len (mVC m1) == len (mVC m2)
                && vcLess (mVC m1) (mVC m2) }
    -> {_ : Proof | processOrder PHIST (Deliver PID m1) (Deliver PID m2) }
@-}

-- | The empty MPA process history observes process local causal delivery. This
-- proof is in this module because it exercises the definition of CHA and
-- forces LH to resolve all the symbols.
{-@ ple emptyPHistObservesPLCD @-}
{-@
emptyPHistObservesPLCD :: p:_ -> ProcessLocalCausalDelivery r {p} {[]} @-}
emptyPHistObservesPLCD :: PID -> Message VCMM r -> Message VCMM r -> Proof
emptyPHistObservesPLCD _p _m1 _m2 = ()




-- * Process order

-- | Process order e→e' indicates that e appears in the subsequence of process
-- history prior to e'.
--
-- ∀e,e',xs. e→e' ⇔ e ∈ …:e':xs
processOrder :: (Eq mm, Eq r) => ProcessHistory mm r -> Event mm r -> Event mm r -> Bool
processOrder hist e e' = listElem e (listTailForHead e' hist)
{-@ reflect processOrder @-}




-- * Process order lemmas

-- | If e₁→e₂ in h, then e₁→e₂ in e₃:h. Consing a new event to the end of a
-- history doesn't change the process order of events already in the history.
--
-- ∀e₁,e₂,e₃,h. e₁→e₂ in h ⇒ e₁→e₂ in e₃:h
{-@
extendProcessOrder
    ::    h:_
    ->   e1:_
    -> { e2:_ | processOrder h e1 e2 }
    ->   e3:_
    -> { processOrder (cons e3 h) e1 e2 }
@-}
extendProcessOrder :: Eq r => H r -> Event VCMM r -> Event VCMM r -> Event VCMM r -> Proof
extendProcessOrder h e₁ e₂ e₃
    {-restate conclusion-}              =   processOrder (e₃:h) e₁ e₂
    {-by def of processOrder-}          === listElem e₁ (listTailForHead e₂ (e₃:h))
    ? premiseLemma
    ? extendElemTail4Head e₁ e₂ h e₃    *** QED
  where premiseLemma
    {-restate premise-}                 =   processOrder h e₁ e₂
    {-by def of processOrder-}          === listElem e₁ (listTailForHead e₂ h)
