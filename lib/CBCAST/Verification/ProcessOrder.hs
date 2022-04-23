{-# OPTIONS_GHC "-Wno-unused-imports" #-} -- LH needs bodies of reflected definitions
{-# OPTIONS_GHC "-Wno-warnings-deprecations" #-} -- Hide the "verification only" and "internal use" warnings

module CBCAST.Verification.ProcessOrder {-# WARNING "Verification only" #-} where

import Language.Haskell.Liquid.ProofCombinators (Proof, (===), (***), QED(..), (?), impossible, (&&&))
import Language.Haskell.Liquid.Properties

import Redefined
import Redefined.Verification
import CBCAST.Core




-- * Process order

{-@ type UniqueProcessHistory r = ProcessHistory<{\x y -> x /= y}> r @-}

-- | Process order e→e' indicates that e appears in the subsequence of process
-- history prior to e'.
--
-- ∀e,e',xs. e→e' ⇔ e ∈ …:e':xs
--
-- Below we prove that when given a history containing distinct events,
-- processOrder is a strict total order. We define processOrder here without
-- such a constraint. This effectively axiomatizes our belief that the list of
-- events contains only unique events, which we will prove in future work.
--
processOrder :: Eq r => ProcessHistory r -> Event r -> Event r -> Bool
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
extendProcessOrder :: Eq r => ProcessHistory r -> Event r -> Event r -> Event r -> Proof
extendProcessOrder h e₁ e₂ e₃
    {-restate premise-}                 =   processOrder h e₁ e₂
    {-by def of processOrder-}          === listElem e₁ (listTailForHead e₂ h)
    ? extendElemTail4Head e₁ e₂ h e₃    === listElem e₁ (listTailForHead e₂ (e₃ : h))
    {-restate conclusion-}              === processOrder (e₃ : h) e₁ e₂
                                        *** QED




-- * procesOrder strict total order

{-@
processOrderIrreflexiveNoPLE :: hs:UniqueProcessHistory r -> Irreflexive (Event r) {processOrder hs} @-}
processOrderIrreflexiveNoPLE :: Eq r => ProcessHistory r -> Event r -> Proof
processOrderIrreflexiveNoPLE [] e =
    {-restate part of conclusion-}      processOrder [] e e
    {-by def of processOrder-}      === listElem e (listTailForHead e [])
    {-by def of listTailForHead-}   === listElem e []
    {-by def of listElem-}          === False
                                    *** QED
processOrderIrreflexiveNoPLE (h:hs) e
  | e == h =
    {-restate part of conclusion-}      processOrder (h:hs) e e
    {-by def of processOrder-}      === listElem e (listTailForHead e (h:hs))
    {-by def of listTailForHead-}   === listElem e hs
    ? uniqueListHeadNotInTail h hs  === False
                                    *** QED
  | e /= h =
    {-restate part of conclusion-}              processOrder (h:hs) e e
    {-by def of processOrder-}              === listElem e (listTailForHead e (h:hs))
    {-by def of listTailForHead-}           === listElem e (listTailForHead e hs)
    {-by def of processOrder-}              === processOrder hs e e
    ? processOrderIrreflexiveNoPLE hs e     === False
                                            *** QED

{-@ ple processOrderIrreflexive @-}
{-@
processOrderIrreflexive :: hs:UniqueProcessHistory r -> Irreflexive (Event r) {processOrder hs} @-}
processOrderIrreflexive :: Eq r => ProcessHistory r -> Event r -> Proof
processOrderIrreflexive [] _e = () -- trivially ¬(e∈[]) holds
processOrderIrreflexive (h:hs) e
    | e == h = uniqueListHeadNotInTail h hs -- uniqueness premise means e≡h ⇒ ¬(e∈hs)
    | e /= h = processOrderIrreflexive hs e -- inductive assumption

{-@ ple processOrderTransitive @-}
{-@
processOrderTransitive :: hs:UniqueProcessHistory r -> Transitive (Event r) {processOrder hs} @-}
processOrderTransitive :: Eq r => ProcessHistory r -> Event r -> Event r -> Event r -> Proof
processOrderTransitive [] _e₁ e₂ _e₃ = impossible $ listElem e₂ [] -- empty history contradicts premise e₂→e₃
processOrderTransitive (h:hs) e₁ e₂ e₃
  | e₂ == h && e₃ == h = impossible $ processOrderIrreflexive (h:hs) h -- irreflexivity contradicts premise e₂→e₃
  | e₂ == h && e₃ /= h = impossible $ truncateElemTail4Head e₂ e₃ hs &&& uniqueListHeadNotInTail e₂ hs -- e₂∈hs contradicts uniqueness premise
  | e₂ /= h && e₃ == h = truncateElemTail4Head e₁ e₂ hs -- tail4e₃≡hs so show e₁∈hs
  | e₂ /= h && e₃ /= h = processOrderTransitive hs e₁ e₂ e₃ -- neither element is at the head of history, so use the inductive assumption

{-@ ple processOrderConnected @-}
{-@
processOrderConnected :: hs:UniqueProcessHistory r -> Connected ({e:Event r | listElem e hs}) {processOrder hs} @-}
processOrderConnected :: Eq r => ProcessHistory r -> Event r -> Event r -> Proof
processOrderConnected [] _e₁ e₂ = impossible $ listElem e₂ [] -- empty history contradicts premise e₁∈hist
processOrderConnected (h:hs) e₁ e₂
  | e₁ == h && e₂ /= h = processOrder (h:hs) e₂ e₁ ? tailElem e₂ h hs *** QED
  | e₁ /= h && e₂ == h = processOrder (h:hs) e₁ e₂ ? tailElem e₁ h hs *** QED
  | e₁ /= h && e₂ /= h = processOrderConnected hs e₁ e₂ -- neither element is at the front of history so use the inductive assumption
