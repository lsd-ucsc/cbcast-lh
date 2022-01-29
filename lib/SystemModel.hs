{-@ LIQUID "--ple" @-}
-- {-# LANGUAGE NoFieldSelectors #-}
{-# LANGUAGE NamedFieldPuns #-}
module SystemModel where

import Language.Haskell.Liquid.ProofCombinators
import Redefined.Fin
import Redefined.Vec



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

{-@ listZipWith :: _ -> xs:_ -> {ys:_ | len xs == len ys} -> {zs:_ | len ys == len zs} @-}
listZipWith :: (a -> b -> c) -> [a] -> [b] -> [c]
listZipWith _ [] [] = []
listZipWith f (x:xs) (y:ys) = f x y : listZipWith f xs ys
{-@ reflect listZipWith @-}

listAnd :: [Bool] -> Bool
listAnd [] = True
listAnd (x:xs) = x && listAnd xs
{-@ reflect listAnd @-}

{- END GENERIC HELPERS -}



{-@ measure procCount :: Nat @-}
{-@ type ProcCount = {n:Nat | n == procCount} @-}

{-@
type PID = Fin {procCount} @-}
type PID = Fin

data Message mm r
    = Message {mMetadata::mm, mRaw::r}
    deriving Eq

data Event mm r
    = Broadcast (Message mm r)
    | Deliver PID (Message mm r)
    deriving Eq

-- | Events are added to the left using cons (:). If events 1, 2, and 3 occur,
-- history will be 3:2:1:[].
type ProcessHistory mm r = [Event mm r]

type Execution mm r = PID -> ProcessHistory mm r

-- | Process order e->e' indicates that e appears in the subsequence of history
-- prior to e'.
processOrder :: (Eq mm, Eq r) => ProcessHistory mm r -> Event mm r -> Event mm r -> Bool
processOrder hist e e' = listElem e (listTailForHead e' hist)
{-@ reflect processOrder @-}



{- BEGIN HYPOTHETICAL SECTION -}

-- | Happens before e->e' indicates one of the following conditions ...
happensBefore :: (Eq mm, Eq r) => Execution mm r -> Event mm r -> Event mm r -> Bool
happensBefore _ _ _ = False
{-@ reflect happensBefore @-}

happensBefore_ :: (Eq mm, Eq r) => Execution mm r -> Event mm r -> Event mm r -> Bool
happensBefore_ exec e e'
    =  forSomePid (\pid -> processOrder (exec pid) e e')
    || case (e, e') of (Broadcast mb, Deliver _ md) -> mb == md; _ -> False
    || forSomeEvent (\e'' -> happensBefore_ exec e e'' && happensBefore_ exec e'' e')
  where
    forSomePid predicate = listOr (listMap predicate {- domain of exec -} undefined)
    forSomeEvent predicate = listOr (listMap predicate (listConcat {- range of exec -} undefined))
    -- These are defined in Data.Assoc and Redefined.List, but we don't need
    -- them here yet.
    listOr :: [Bool] -> Bool
    listOr = undefined
    listMap :: (a -> b) -> [a] -> [b]
    listMap = undefined
    listConcat :: [[a]] -> [a]
    listConcat = undefined
{-@ ignore happensBefore_ @-} -- Can't define HB this way (termination).

{-@
type CausalDelivery mm r X
    =   p  : PID
    ->  q  : PID
    ->  r  : PID
    -> {m1 : Message mm r | listElem (Broadcast m1) (X q) && listElem (Deliver p m1) (X p)}
    -> {m2 : Message mm r | listElem (Broadcast m2) (X r) && listElem (Deliver p m2) (X p)}
    -> {_  : Proof | happensBefore X (Broadcast m1) (Broadcast m2)}
    -> {_  : Proof | processOrder (X p) (Deliver p m1) (Deliver p m2)}
@-}

x0 :: Execution mm r
x0 _ = []
{-@ reflect x0 @-}

{-@
x0ObservesCausalDelivery :: CausalDelivery mm r {x0} @-}
x0ObservesCausalDelivery :: PID -> PID -> PID -> Message mm r -> Message mm r -> Proof -> Proof
x0ObservesCausalDelivery _p _q _r _m1 _m2 () = ()

{- END HYPOTHETICAL SECTION -}



{-@
type Clock = {c:Integer | 0 <= c} @-}
type Clock = Integer

{-@
type VC = Vec Clock {procCount} @-}
type VC = Vec Clock

{-@
vcSize :: VC -> ProcCount @-}
vcSize :: VC -> Int
vcSize = listLength
{-@ reflect vcSize @-}

{-@
vcLessEqual :: VC -> VC -> Bool @-}
vcLessEqual :: VC -> VC -> Bool
vcLessEqual a b = listAnd (listZipWith vcLessEqualHelper a b)
{-@ reflect vcLessEqual @-}
vcLessEqualHelper :: Clock -> Clock -> Bool
vcLessEqualHelper a b = a <= b
{-@ reflect vcLessEqualHelper @-}

{-@
vcLess :: VC -> VC -> Bool @-}
vcLess :: VC -> VC -> Bool
vcLess a b = vcLessEqual a b && a /= b
{-@ reflect vcLess @-}

{-@
vcConcurrent :: VC -> VC -> Bool @-}
vcConcurrent :: VC -> VC -> Bool
vcConcurrent a b = not (vcLess a b) && not (vcLess b a)
{-@ reflect vcConcurrent @-}



{- BEGIN HYPOTHETICAL SECTION -}

-- FIXME: we can't actually define VC-HB-copacetic because it requires looking
-- up VC(e) on events. The draft says that for VC(k), k may be a node, a
-- message, or an event. For an event, VC(e) is the time the event was added to
-- process history. That's wrong. We need an alternate definition of VC-HB
-- copacetic.
--
-- eventVC :: Event mm r -> VC
-- eventVC (Broadcast m) = ???
-- eventVC (Deliver _ m) = ???
--
-- We want to say that event-VCs correspond to message VCs, but that's wrong
-- because events don't have VCs. Maybe instead we need to say something like
-- VCs on messages?
--
-- TODO: should be IFF not ->
-- {-@
-- type VCHBCopacetic X
--     =   q  : PID
--     ->  r  : PID
--     -> {e1 : Event mm r | listElem e1 (X q)}
--     -> {e2 : Event mm r | listElem e2 (X r)}
--     -> {_  : Proof | vcLess (eventVC e1) (eventVC e2)}
--     -> {_  : Proof | happensBefore X e1 e2 }
-- @-}

{- END HYPOTHETICAL SECTION -}



-- | Metadata for messages in a MPA which uses VCs.
{-@
data VCMM = VCMM {sender::PID, sent::VC} @-}
data VCMM = VCMM {sender::PID, sent::VC}

-- | Message type for a MPA which uses VCs.
{-@
type M r = Message VCMM r @-}
type M r = Message VCMM r

{-@
sentVC :: M r -> VC @-}
sentVC :: M r -> VC
sentVC Message{mMetadata=VCMM{sent}} = sent
{-@ reflect sentVC @-}

{-@
type ProcessLocalCausalDelivery r P H
    =  {m1 : M r | listElem (Deliver P m1) H }
    -> {m2 : M r | listElem (Deliver P m2) H
                && vcLess (sentVC m1) (sentVC m2) }
    -> {_ : Proof | processOrder H (Deliver P m1) (Deliver P m2) }
@-}

{-@
h0 :: ProcessHistory VCMM r @-}
h0 :: ProcessHistory VCMM r
h0 = []
{-@ reflect h0 @-}

{-@
h0ObservesPLCD :: ProcessLocalCausalDelivery r {999} {h0} @-}
h0ObservesPLCD :: M r -> M r -> Proof
h0ObservesPLCD _m1 _m2 = () *** QED

-- (backburner) PLCDImpliesCD
-- (backburner) VCISO: cbcast implies vc-hb-copacetic
-- (NEXT!)      CBCAST observes PLCD
-- (backburner) CBCAST observes CD
