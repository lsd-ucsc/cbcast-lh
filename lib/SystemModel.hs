{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}
module SystemModel where

import Language.Haskell.Liquid.ProofCombinators
import Redefined.Fin
import Redefined.Vec ()




{- BEGIN GENERIC HELPERS (move back to other modules later) -}

{-@ listLength :: xs:_ -> {v:Nat | v == len xs } @-}
listLength :: [a] -> Int
listLength [] = 0
listLength (_x:xs) = 1 + listLength xs
{-@ measure listLength @-}

listElem :: Eq a => a -> [a] -> Bool
listElem _ [] = False
listElem e (x:xs) = e==x || listElem e xs
{-@ reflect listElem @-}

listTailForHead :: Eq a => a -> [a] -> [a]
listTailForHead _ [] = []
listTailForHead e (x:xs) = if e==x then xs else listTailForHead e xs
{-@ reflect listTailForHead @-}

{-@ listIndex :: xs:[a] -> Fin {len xs} -> a @-}
listIndex :: [a] -> Int -> a
listIndex (x:xs) i = if i==0 then x else listIndex xs (i-1)
{-@ reflect listIndex @-}

listAnd :: [Bool] -> Bool
listAnd [] = True
listAnd (x:xs) = x && listAnd xs
{-@ reflect listAnd @-}

{-@ listZipWith :: _ ->  xs:_
                     -> {ys:_ | len xs == len ys}
                     -> {zs:_ |           len ys == len zs} @-}
listZipWith :: (a -> b -> c) -> [a] -> [b] -> [c]
listZipWith _ [] [] = []
listZipWith f (x:xs) (y:ys) = f x y : listZipWith f xs ys
{-@ reflect listZipWith @-}

-- Used by UCausalDelivery.deliverable
{-@ listZipWith3 :: _ ->  ws:_
                      -> {xs:_ | len ws == len xs}
                      -> {ys:_ |           len xs == len ys}
                      -> {zs:_ |                     len ys == len zs} @-}
listZipWith3 :: (a -> b -> c -> d) -> [a] -> [b] -> [c] -> [d]
listZipWith3 _ [] [] [] = []
listZipWith3 f (x:xs) (y:ys) (z:zs) = f x y z : listZipWith3 f xs ys zs
{-@ reflect listZipWith3 @-}

{- END GENERIC HELPERS -}




{-@
type PID = Nat @-}
type PID = Fin
{-@ type PIDsized N = Fin {N} @-}

{-@
data Message mm r = Message {mMetadata::mm, mRaw::r} @-}
data Message mm r = Message {mMetadata::mm, mRaw::r}
    deriving Eq

data Event mm r
    = Broadcast (Message mm r)
    | Deliver PID (Message mm r)
    deriving Eq

-- | Events are added to the left using cons (:). If events 1, 2, and 3 occur,
-- history will be 3:2:1:[].
type ProcessHistory mm r = [Event mm r]

-- | Process order e->e' indicates that e appears in the subsequence of history
-- prior to e'.
processOrder :: (Eq mm, Eq r) => ProcessHistory mm r -> Event mm r -> Event mm r -> Bool
processOrder hist e e' = listElem e (listTailForHead e' hist)
{-@ reflect processOrder @-}




{- BEGIN HYPOTHETICAL SECTION -}
--
-- This code is mostly fine. It just needs some finesse.
--
-- Focus: executions, happens before
--
-- Issues:
--
--  1. Happens before requires that we talk about PIDs being "in the domain" of
--  an execution (so a map or assoc would be more convenient than a function)
--  and it also requires that we extract process histories via PIDs from the
--  execution (so a function would be more convenient than a map).
--
--  2. Happens before is defined as one of three cases, two of which rely on
--  ∃'ing variables into existence, so we need a bunch of extra functions to
--  test a predicate with every possible answer (from within the execution).
--
-- type Execution mm r = PID -> ProcessHistory mm r
-- 
-- -- | Happens before e->e' indicates one of the following conditions ...
-- happensBefore :: (Eq mm, Eq r) => Execution mm r -> Event mm r -> Event mm r -> Bool
-- happensBefore _ _ _ = False
-- {-@ reflect happensBefore @-}
-- 
-- happensBefore_ :: (Eq mm, Eq r) => Execution mm r -> Event mm r -> Event mm r -> Bool
-- happensBefore_ exec e e'
--     =  forSomePid (\pid -> processOrder (exec pid) e e')
--     || case (e, e') of (Broadcast mb, Deliver _ md) -> mb == md; _ -> False
--     || forSomeEvent (\e'' -> happensBefore_ exec e e'' && happensBefore_ exec e'' e')
--   where
--     forSomePid predicate = listOr (listMap predicate {- domain of exec -} undefined)
--     forSomeEvent predicate = listOr (listMap predicate (listConcat {- range of exec -} undefined))
--     -- These are defined in Data.Assoc and Redefined.List, but we don't need
--     -- them here yet.
--     listOr :: [Bool] -> Bool
--     listOr = undefined
--     listMap :: (a -> b) -> [a] -> [b]
--     listMap = undefined
--     listConcat :: [[a]] -> [a]
--     listConcat = undefined
-- {-@ ignore happensBefore_ @-} -- Can't define HB this way (termination).
-- 
-- {-@
-- type CausalDelivery mm r X
--     =   p  : PID
--     ->  q  : PID
--     ->  r  : PID
--     -> {m1 : Message mm r | listElem (Broadcast m1) (X q) && listElem (Deliver p m1) (X p)}
--     -> {m2 : Message mm r | listElem (Broadcast m2) (X r) && listElem (Deliver p m2) (X p)}
--     -> {_  : Proof | happensBefore X (Broadcast m1) (Broadcast m2)}
--     -> {_  : Proof | processOrder (X p) (Deliver p m1) (Deliver p m2)}
-- @-}
-- 
-- x0 :: Execution mm r
-- x0 _ = []
-- {-@ reflect x0 @-}
-- 
-- {-@
-- x0ObservesCausalDelivery :: CausalDelivery mm r {x0} @-}
-- x0ObservesCausalDelivery :: PID -> PID -> PID -> Message mm r -> Message mm r -> Proof -> Proof
-- x0ObservesCausalDelivery _p _q _r _m1 _m2 () = ()
--
{- END HYPOTHETICAL SECTION -}




{-@
type Clock = {c:Integer | 0 <= c} @-}
type Clock = Integer

{-@
type VC = [Clock] @-}
type VC = [Clock]
{-@ type VCsized N = {v:VC | len v == N} @-}
{-@ type VCasV V = VCsized {len V} @-}

{-@ type PIDasV V = Fin {len V} @-}

-- QQQ: everywhere a *asV type is defined, we call len, but perhaps we should
-- alias that here to vcSize
--
-- QQQ: similarly, everywhere we deal with proccount we specify Nat on the LH
-- side and Int on the haskell side; perhaps we should have a type alias here
-- (or up by PID?)

{-@
vcLessEqual :: v:VC -> VCasV {v} -> Bool @-}
vcLessEqual :: VC -> VC -> Bool
vcLessEqual a b = listAnd (listZipWith vcLessEqualHelper a b)
{-@ reflect vcLessEqual @-}
vcLessEqualHelper :: Clock -> Clock -> Bool
vcLessEqualHelper a b = a <= b
{-@ reflect vcLessEqualHelper @-}

{-@
vcLess :: v:VC -> VCasV {v} -> Bool @-}
vcLess :: VC -> VC -> Bool
vcLess a b = vcLessEqual a b && a /= b
{-@ reflect vcLess @-}

{-@
vcConcurrent :: v:VC -> VCasV {v} -> Bool @-}
vcConcurrent :: VC -> VC -> Bool
vcConcurrent a b = not (vcLess a b) && not (vcLess b a)
{-@ reflect vcConcurrent @-}




{- BEGIN HYPOTHETICAL SECTION -}
--
-- VC-HB-copacetic is ill defined. Thankfully, this isn't required for our
-- first mechanization push.
--
-- Focus: VC-HB-copacetic, VCs for events (?)
--
-- Issues:
--
--  1. VC-HB-copacetic is defined somewhat lazily in terms of events with
--  vector clocks, but events in process histories don't have vector clocks.
--
--  2. In the next section, messages are defined to have vector clocks (so
--  maybe vc-hb-copacetic should be defined later anyway), but it's not clear
--  if message vector clocks (broadcast time) is good enough for defining
--  VC-HB-copacetic. More thought is needed.
--
-- eventVC :: Event mm r -> VC
-- eventVC (Broadcast m) = ???
-- eventVC (Deliver _ m) = ???
--
-- FIXME: should be <-> not ->
-- {-@
-- type VCHBCopacetic X
--     =   q  : PID
--     ->  r  : PID
--     -> {e1 : Event mm r | listElem e1 (X q)}
--     -> {e2 : Event mm r | listElem e2 (X r)}
--     -> {_  : Proof | vcLess (eventVC e1) (eventVC e2)}
--     -> {_  : Proof | happensBefore X e1 e2 }
-- @-}
--
{- END HYPOTHETICAL SECTION -}




-- QQQ: Does this belong to the system model (because it's cbcast agnostic) or
-- to the MPA (because the stuff about proccount is very much specific to
-- cbcast)?

-- | Message metadata for a MPA which uses VCs.
{-@
data VCMM = VCMM {vcmmSent::VC, vcmmSender::PIDasV {vcmmSent}} @-}
data VCMM = VCMM {vcmmSent::VC, vcmmSender::PID}
    deriving Eq

-- NOTE: these accessors are convenience functions to look through the Message
-- to the VCMM. Getting them to work correctly in specifications required
-- either measure or inline (not reflect). Also, for some reason they couldn't
-- be defined using record-pattern-matches.

{-@
mVC :: Message VCMM r -> VC @-}
mVC :: Message VCMM r -> VC
mVC m = vcmmSent (mMetadata m) -- Cannot be defined with pattern matching
{-@ inline mVC @-}

{-@
mSender :: m:Message VCMM r -> PIDsized {len (mVC m)} @-}
mSender :: Message VCMM r -> PID
mSender m = vcmmSender (mMetadata m) -- QQQ: Why can't this be defined with pattern matching?
{-@ inline mSender @-}

{-@
type ProcessLocalCausalDelivery r PID PHIST
    =  {m1 : Message VCMM r | listElem (Deliver PID m1) PHIST }
    -> {m2 : Message VCMM r | listElem (Deliver PID m2) PHIST
                && len (mVC m1) == len (mVC m2)
                && vcLess (mVC m1) (mVC m2) }
    -> {_ : Proof | processOrder PHIST (Deliver PID m1) (Deliver PID m2) }
@-}

{-@ ple emptyPHistObservesPLCD @-}
{-@
emptyPHistObservesPLCD :: p:_ -> ProcessLocalCausalDelivery r {p} {[]} @-}
emptyPHistObservesPLCD :: PID -> Message VCMM r -> Message VCMM r -> Proof
emptyPHistObservesPLCD _p _m1 _m2 = ()
