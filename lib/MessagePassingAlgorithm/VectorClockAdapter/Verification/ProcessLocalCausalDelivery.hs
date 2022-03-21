{-# OPTIONS_GHC "-Wno-unused-imports" #-} -- LH needs bodies of reflected definitions

-- Process local causal delivery definition for a process history.
module MessagePassingAlgorithm.VectorClockAdapter.Verification.ProcessLocalCausalDelivery where

import Language.Haskell.Liquid.ProofCombinators
import Language.Haskell.Liquid.Properties

import Redefined
import VectorClock
import MessagePassingAlgorithm
import MessagePassingAlgorithm.VectorClockAdapter

import Redefined.Verification

{-@
type ProcessLocalCausalDelivery r PID PHIST
    =  {m1 : M r         | listElem (Deliver PID m1) PHIST }
    -> {m2 : MasM r {m1} | listElem (Deliver PID m2) PHIST
                && vcLess (mVC m1) (mVC m2) }
    -> {_ : Proof | processOrder2 PHIST (Deliver PID m1) (Deliver PID m2) }
@-}

-- | The empty MPA process history observes process local causal delivery. This
-- proof is in this module because it exercises the definition of CHA and
-- forces LH to resolve all the symbols.
{-@ ple emptyPHistObservesPLCD @-}
{-@
emptyPHistObservesPLCD :: p:_ -> ProcessLocalCausalDelivery r {p} {[]} @-}
emptyPHistObservesPLCD :: PID -> M r -> M r -> Proof
emptyPHistObservesPLCD _p _m1 _m2 = ()




-- * Process order

-- | Process order defined without the constraint on events being unique. This
-- effectively axiomatizes our belief that the list of events contains unique
-- events, which we will prove in future work.
processOrder :: (Eq mm, Eq r) => ProcessHistory mm r -> Event mm r -> Event mm r -> Bool
processOrder hist e e' = listElem e (listTailForHead e' hist)
{-@ reflect processOrder @-}

{-@ type UniqueProcessHistory mm r = ProcessHistory<{\x y -> x /= y}> mm r @-}

-- | Process order e→e' indicates that e appears in the subsequence of process
-- history prior to e'.
--
-- ∀e,e',xs. e→e' ⇔ e ∈ …:e':xs
{-@
processOrder2 :: UniqueProcessHistory mm r -> _ -> _ -> _ @-}
processOrder2 :: (Eq mm, Eq r) => ProcessHistory mm r -> Event mm r -> Event mm r -> Bool
processOrder2 hist e e' = listElem e (listTailForHead e' hist)
{-@ reflect processOrder2 @-}




-- * Process order lemmas

-- | If e₁→e₂ in h, then e₁→e₂ in e₃:h. Consing a new event to the end of a
-- history doesn't change the process order of events already in the history.
--
-- ∀e₁,e₂,e₃,h. e₁→e₂ in h ⇒ e₁→e₂ in e₃:h
{-@
extendProcessOrder
    ::    h:UniqueProcessHistory mm r
    ->   e1:_
    -> { e2:_ | processOrder2 h e1 e2 }
    -> { e3:_ | not (listElem e3 h) }
    -> { processOrder2 (cons e3 h) e1 e2 }
@-}
extendProcessOrder :: (Eq mm, Eq r) => ProcessHistory mm r -> Event mm r -> Event mm r -> Event mm r -> Proof
extendProcessOrder h e₁ e₂ e₃
    {-restate premise-}                 =   processOrder2 h e₁ e₂
    {-by def of processOrder2-}          === listElem e₁ (listTailForHead e₂ h)
    ? extendElemTail4Head e₁ e₂ h e₃    === listElem e₁ (listTailForHead e₂ (e₃ `uCons` h))
    {-restate conclusion-}              === processOrder2 (e₃ `uCons` h) e₁ e₂
                                        *** QED




-- * procesOrder strict total order

{-@
processOrderIrreflexiveNoPLE :: hs:UniqueProcessHistory mm r -> Irreflexive (Event mm r) {processOrder2 hs} @-}
processOrderIrreflexiveNoPLE :: (Eq mm, Eq r) => ProcessHistory mm r -> Event mm r -> Proof
processOrderIrreflexiveNoPLE [] e =
    {-restate part of conclusion-}      processOrder2 [] e e
    {-by def of processOrder2-}      === listElem e (listTailForHead e [])
    {-by def of listTailForHead-}   === listElem e []
    {-by def of listElem-}          === False
                                    *** QED
processOrderIrreflexiveNoPLE (h:hs) e
  | e == h =
    {-restate part of conclusion-}      processOrder2 (h:hs) e e
    {-by def of processOrder2-}      === listElem e (listTailForHead e (h:hs))
    {-by def of listTailForHead-}   === listElem e hs
    ? uniqueListHeadNotInTail h hs  === False
                                    *** QED
  | e /= h =
    {-restate part of conclusion-}              processOrder2 (h:hs) e e
    {-by def of processOrder2-}              === listElem e (listTailForHead e (h:hs))
    {-by def of listTailForHead-}           === listElem e (listTailForHead e hs)
    {-by def of processOrder2-}              === processOrder2 hs e e
    ? processOrderIrreflexiveNoPLE hs e     === False
                                            *** QED

{-@ ple processOrderIrreflexive @-}
{-@
processOrderIrreflexive :: hs:UniqueProcessHistory mm r -> Irreflexive (Event mm r) {processOrder2 hs} @-}
processOrderIrreflexive :: (Eq mm, Eq r) => ProcessHistory mm r -> Event mm r -> Proof
processOrderIrreflexive [] _e = () -- trivially ¬(e∈[]) holds
processOrderIrreflexive (h:hs) e
    | e == h = uniqueListHeadNotInTail h hs -- uniqueness premise means e≡h ⇒ ¬(e∈hs)
    | e /= h = processOrderIrreflexive hs e -- inductive assumption

{-@ ple processOrderTransitive @-}
{-@
processOrderTransitive :: hs:UniqueProcessHistory mm r -> Transitive (Event mm r) {processOrder2 hs} @-}
processOrderTransitive :: (Eq mm, Eq r) => ProcessHistory mm r -> Event mm r -> Event mm r -> Event mm r -> Proof
processOrderTransitive [] _e₁ e₂ _e₃ = impossible $ listElem e₂ [] -- empty history contradicts premise e₂→e₃
processOrderTransitive (h:hs) e₁ e₂ e₃
  | e₂ == h && e₃ == h = impossible $ processOrderIrreflexive (h:hs) h -- irreflexivity contradicts premise e₂→e₃
  | e₂ == h && e₃ /= h = impossible $ truncateElemTail4Head e₂ e₃ hs &&& uniqueListHeadNotInTail e₂ hs -- e₂∈hs contradicts uniqueness premise
  | e₂ /= h && e₃ == h = truncateElemTail4Head e₁ e₂ hs -- tail4e₃≡hs so show e₁∈hs
  | e₂ /= h && e₃ /= h = processOrderTransitive hs e₁ e₂ e₃ -- neither element is at the head of history, so use the inductive assumption

{-@ ple processOrderConnected @-}
{-@
processOrderConnected :: hs:UniqueProcessHistory mm r -> Connected ({e:Event mm r | listElem e hs}) {processOrder2 hs} @-}
processOrderConnected :: (Eq mm, Eq r) => ProcessHistory mm r -> Event mm r -> Event mm r -> Proof
processOrderConnected [] _e₁ e₂ = impossible $ listElem e₂ [] -- empty history contradicts premise e₁∈hist
processOrderConnected (h:hs) e₁ e₂
  | e₁ == h && e₂ /= h = processOrder2 (h:hs) e₂ e₁ ? tailElem e₂ h hs *** QED
  | e₁ /= h && e₂ == h = processOrder2 (h:hs) e₁ e₂ ? tailElem e₁ h hs *** QED
  | e₁ /= h && e₂ /= h = processOrderConnected hs e₁ e₂ -- neither element is at the front of history so use the inductive assumption
