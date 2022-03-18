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




-- * procesOrder strict total order

{-@ type UniqueProcessHistory mm r = ProcessHistory<{\x y -> x /= y}> mm r @-}

{-@
processOrder2 :: UniqueProcessHistory mm r -> _ -> _ -> _ @-}
processOrder2 :: (Eq mm, Eq r) => ProcessHistory mm r -> Event mm r -> Event mm r -> Bool
processOrder2 hist e e' = listElem e (listTailForHead e' hist)
{-@ reflect processOrder2 @-}

{-@
uniqueListHeadNotInTail' :: {xs:[a]<{\j k -> j /= k}> | xs /= []} -> {not (listElem (head xs) (tail xs))} @-}
uniqueListHeadNotInTail' :: Eq a => [a] -> Proof
uniqueListHeadNotInTail' (x:xs) = uniqueListHeadNotInTail x xs

-- | The head is not in the tail of a list containing unique elements. This
-- type looks weird, but the relationship between e and xs is exactly what a
-- unique list expresses (see (uniqueListHeadNotInTail'@). The purpose of
-- keeping this lemma around is it allows callers to call with arguments that
-- don't prove the list is nonempty.
{-@
uniqueListHeadNotInTail
    :: e:a -> xs:[{x:a | e /= x}] -> {not (listElem e xs)} @-}
uniqueListHeadNotInTail :: Eq a => a -> [a] -> Proof
uniqueListHeadNotInTail e [] = listElem e [] *** QED
uniqueListHeadNotInTail e (x:xs) =
        listElem e (x:xs)
    === (e==x || listElem e xs)
    === listElem e xs
        ? uniqueListHeadNotInTail e xs
    *** QED

{-@
processOrder2IrreflexiveNoPLE :: hs:UniqueProcessHistory mm r -> Irreflexive (Event mm r) {processOrder2 hs} @-}
processOrder2IrreflexiveNoPLE :: (Eq mm, Eq r) => ProcessHistory mm r -> Event mm r -> Proof
processOrder2IrreflexiveNoPLE [] e =
    {-restate part of conclusion-}      processOrder2 [] e e
    {-by def of processOrder2-}     === listElem e (listTailForHead e [])
    {-by def of listTailForHead-}   === listElem e []
    {-by def of listElem-}          === False
                                    *** QED
processOrder2IrreflexiveNoPLE (h:hs) e
  | e == h =
    {-restate part of conclusion-}      processOrder2 (h:hs) e e
    {-by def of processOrder2-}     === listElem e (listTailForHead e (h:hs))
    {-by def of listTailForHead-}   === listElem e hs
    ? uniqueListHeadNotInTail h hs  === False
                                    *** QED
  | e /= h =
    {-restate part of conclusion-}              processOrder2 (h:hs) e e
    {-by def of processOrder2-}             === listElem e (listTailForHead e (h:hs))
    {-by def of listTailForHead-}           === listElem e (listTailForHead e hs)
    {-by def of processORder2-}             === processOrder2 hs e e
    ? processOrder2IrreflexiveNoPLE hs e    === False
                                            *** QED

{-@ ple processOrder2Irreflexive @-}
{-@
processOrder2Irreflexive :: hs:UniqueProcessHistory mm r -> Irreflexive (Event mm r) {processOrder2 hs} @-}
processOrder2Irreflexive :: (Eq mm, Eq r) => ProcessHistory mm r -> Event mm r -> Proof
processOrder2Irreflexive [] _e = ()
processOrder2Irreflexive (h:hs) e
    | e == h = uniqueListHeadNotInTail h hs
    | e /= h = processOrder2Irreflexive hs e

{-@ ple processOrder2Transitive @-}
{-@
processOrder2Transitive :: hs:UniqueProcessHistory mm r -> Transitive (Event mm r) {processOrder2 hs} @-}
processOrder2Transitive :: (Eq mm, Eq r) => ProcessHistory mm r -> Event mm r -> Event mm r -> Event mm r -> Proof
processOrder2Transitive [] _e₁ e₂ _e₃ = impossible $ listElem e₂ [] -- contradicts premise e₂→e₃
processOrder2Transitive (h:hs) e₁ e₂ e₃
  | e₂ == h && e₃ == h = impossible $ processOrder2Irreflexive (h:hs) h -- contradicts premise e₂→e₃
  | e₂ == h && e₃ /= h = impossible $ truncateElemTail4Head e₂ e₃ hs &&& uniqueListHeadNotInTail e₂ hs -- in this case e₂≡h ∧ e₂∈hs
  | e₂ /= h && e₃ == h = truncateElemTail4Head e₁ e₂ hs -- in this case tail4e₃≡hs so show e₁∈hs
  | e₂ /= h && e₃ /= h = processOrder2Transitive hs e₁ e₂ e₃ -- neither element is at the head of history, so use the inductive assumption
