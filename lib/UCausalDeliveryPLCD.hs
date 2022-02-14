{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}
{-# OPTIONS_GHC "-Wno-unused-imports" #-} -- LH needs Redefined.Ord
module UCausalDeliveryPLCD where

import Language.Haskell.Liquid.ProofCombinators
import Redefined.Fin
import Redefined.Ord
-- import Redefined.Proof (proofConst)

import SystemModel
import Properties
import UCausalDelivery
import Properties2




-- * Empty values

-- | The empty, initial, vc₀, vector clock.
{-@
vcEmpty :: n:Nat -> VCsized {n} @-}
vcEmpty :: Int -> VC
vcEmpty 0 = []
vcEmpty n = 0 : vcEmpty (n - 1)
{-@ reflect vcEmpty @-}

-- | The empty, initial, p₀, for processes.
{-@
pEmpty :: n:Nat -> PIDsized {n} -> Psized r {n} @-}
pEmpty :: Int -> Fin -> P r
pEmpty n p_id = P{pVC=vcEmpty n, pID=p_id, pDQ=[], pHist=[]}
{-@ reflect pEmpty @-}




-- * Shims

-- | The deliver function, but throw away the message.
{-@ deliverShim :: p:P r -> PasP r {p} @-}
deliverShim :: P r -> P r
deliverShim p =
    case deliver p of
        Nothing -> p
        Just (_, p') -> p'
{-@ reflect deliverShim @-}

-- | The broadcast function, but throw away the message.
{-@ broadcastShim :: r -> p:P r -> PasP r {p} @-}
broadcastShim :: r -> P r -> P r
broadcastShim raw p =
    let (_, p') = broadcast raw p in p'
{-@ reflect broadcastShim @-}




-- * Clock-History agreement

-- ** CHA property

-- | The vc for the message in an event.
{-@
eventVC :: n:Nat -> Event (VCMMsized {n}) r -> VCsized {n} @-}
eventVC :: Int -> Event VCMM r -> VC
eventVC _n (Broadcast m) = vcmmSent (mMetadata m) -- QQQ: Why can't we use mVC here?
eventVC _n (Deliver _pid m) = vcmmSent (mMetadata m)
{-@ reflect eventVC @-}

-- | The supremum of vector clocks on events in a process history.
{-@
pHistVC :: p:P r -> VCasP {p} @-}
pHistVC :: P r -> VC
pHistVC p = pHistVCHelper (listLength (pVC p)) (pHist p)
{-@ reflect pHistVC @-}
{-@
pHistVCHelper :: n:Nat -> Hsized r {n} -> VCsized {n} @-}
pHistVCHelper :: Int -> H r -> VC
pHistVCHelper n [] = vcEmpty n
pHistVCHelper n (e:es) = eventVC n e `vcCombine` pHistVCHelper n es
{-@ reflect pHistVCHelper @-}

{-@
type ClockHistoryAgreement P
    = {_ : Proof | vcLessEqual (pHistVC P) (pVC P) }
@-}

{-@ ple pEmptyCHA @-}
{-@
pEmptyCHA :: n:Nat -> p_id:PIDsized {n} -> ClockHistoryAgreement {pEmpty n p_id} @-}
pEmptyCHA :: Int -> Fin -> Proof
pEmptyCHA n p_id
    =   let p = pEmpty n p_id
    in  vcLessEqual (pHistVC p) (pVC p) -- restate conclusion
        ? vcLessEqualReflexive (vcEmpty n)
    *** QED




-- ** CHA preservation

{-@
type CHApreservation r N OP
    =  p:Psized r {N}
    -> ClockHistoryAgreement {p}
    -> ClockHistoryAgreement {OP p}
@-}

-- *** receive

{-@ ple receiveCHApres @-}
{-@
receiveCHApres :: m:M r -> CHApreservation r {len (mVC m)} {receive m} @-}
receiveCHApres :: M r -> P r -> Proof -> Proof
receiveCHApres m p _pCHA
    | mSender m == pID p = () -- pHist is unchanged
    | otherwise = () -- pHist is unchanged

-- *** deliver

{-@ ple deliverVcIsPrevCombineMsg @-}
{-@
deliverVcIsPrevCombineMsg
    :: {p1:P r | isJust (deliver p1)}
    -> { m:M r | fst (fromJust (deliver p1)) == m }
    -> {p2:P r | snd (fromJust (deliver p1)) == p2}
    -> {vcCombine (pVC p1) (mVC m) == pVC p2}
@-}
deliverVcIsPrevCombineMsg :: P r -> M r -> P r -> Proof
deliverVcIsPrevCombineMsg p₁ m p₂ = --- by cases of deliver
    case dequeue (pVC p₁) (pDQ p₁) of -- by cases of deliver
        Just (_m, _pDQ') -> -- one case, due to premise
                pVC p₂ -- restate (part of) conclusion
            === vcCombine (pVC p₁) (mVC m) -- by def of deliver
            *** QED

{-@ ple deliverHistVcIsPrevCombineMsg @-}
{-@
deliverHistVcIsPrevCombineMsg
    :: {p1:P r | isJust (deliver p1)}
    -> { m:M r | fst (fromJust (deliver p1)) == m }
    -> {p2:P r | snd (fromJust (deliver p1)) == p2}
    -> {vcCombine (pHistVC p1) (mVC m) == pHistVC p2}
@-}
deliverHistVcIsPrevCombineMsg :: P r -> M r -> P r -> Proof
deliverHistVcIsPrevCombineMsg p₁ m p₂ =
    case dequeue (pVC p₁) (pDQ p₁) of -- by cases of deliver
        Just (_m, _pDQ') -> -- one case, due to premise
            let n = listLength (pVC p₁)
                e = Deliver (pID p₁) (coerce m)
            in  pHistVC p₂ -- restate (part of) conclusion
                ? ( pVC p₂ === vcCombine (pVC p₁) (mVC m) ) -- VCs have same length
            === pHistVCHelper n (pHist p₂) -- by def of pHistVC
                ? ( pHist p₂ === e : pHist p₁ )
            === pHistVCHelper n (e : pHist p₁) -- by def of deliver
            === vcCombine (eventVC n e) (pHistVCHelper n (pHist p₁)) -- by def of pHistVCHelper
                ? (eventVC n e === mVC m)
            === vcCombine (mVC m) (pHistVCHelper n (pHist p₁))
            === vcCombine (mVC m) (pHistVC p₁)
                ? vcCombineCommutativity n (mVC m) (pHistVC p₁)
            === vcCombine (pHistVC p₁) (mVC m)
            *** QED

{-@ ple deliverCHApres @-}
{-@
deliverCHApres :: n:Nat -> CHApreservation r {n} {deliverShim} @-}
deliverCHApres :: Int -> P r -> Proof -> Proof
deliverCHApres n p _pCHA = -- by cases of deliver
    case dequeue (pVC p) (pDQ p) of
        Nothing -> () -- p is unchanged
        Just (m, _pDQ) ->
            let p' = deliverShim p in
                vcLessEqual (pHistVC p') (pVC p') -- restate conclusion
                ? deliverVcIsPrevCombineMsg p m p'
                ? deliverHistVcIsPrevCombineMsg p m p'
            === vcLessEqual (pHistVC p `vcCombine` mVC m) (pVC p `vcCombine` mVC m)
            --- vcLessEqual (pHistVC p) (pVC p) -- restate premise
                ? vcCombineVCLessEqualMonotonicLeft n (pHistVC p) (pVC p) (mVC m)
            *** QED

-- *** broadcast

{-@
broadcastCHApres :: raw:r -> n:Nat -> CHApreservation r {n} {broadcastShim raw} @-}
broadcastCHApres :: r -> Int -> P r -> Proof -> Proof
broadcastCHApres _raw _n _p _pCHA
    -- CHA says that p_hist_vc <= p_vc
    =   () *** Admit





-- * Process Local Causal Delivery

-- ** PLCD alias for P

-- An alias for the system model's PLCD in terms of the MPA's process type.
{-@
type PLCD r P
    = ProcessLocalCausalDelivery r {pID P} {pHist P}
@-}

{-@ ple pEmptyPLCD @-}
{-@
pEmptyPLCD :: n:Nat -> p_id:PIDsized {n} -> PLCD r {pEmpty n p_id} @-}
pEmptyPLCD :: Eq r => Int -> Fin -> (M r -> M r -> Proof)
-- pEmptyPLCD _n _p_id _m1 _m2 = () -- Premises don't hold.
-- NOTE: can comment the proof below
pEmptyPLCD n p_id m1 _m2
    =   True
    --- QQQ: Why doesn't this premise report as True without PLE?
    === listElem (Deliver p_id m1) (pHist (pEmpty n p_id)) -- restate a premise
    --- QQQ: Why doesn't expanding the definition of pEmpty work without PLE?
    === listElem (Deliver p_id m1) (pHist P{pVC=vcEmpty n, pID=p_id, pDQ=[], pHist=[]}) -- by def of pEmpty
    === listElem (Deliver p_id m1) [] -- by def of pHist
    === False -- by def of listElem
    *** QED -- premise failed




-- ** PLCD preservation

{-@
type PLCDpreservation r N OP
    =  p:Psized r {N}
    -> PLCD r {p}
    -> PLCD r {OP p}
@-}

-- *** receive

{-@ ple receivePreservesIDandHist @-}
{-@
receivePreservesIDandHist :: m:M r -> p:PasM r {m} -> { pID p == pID (receive m p)
                                                     && pHist p == pHist (receive m p) } @-}
receivePreservesIDandHist :: M r -> P r -> Proof
receivePreservesIDandHist m p -- by cases from receive
    | mSender m == pID p = ()
    | otherwise = ()

{-@ ple receivePLCDpres @-}
{-@
receivePLCDpres :: m:M r -> PLCDpreservation r {len (mVC m)} {receive m} @-}
receivePLCDpres :: Eq r => M r -> P r -> (M r -> M r -> Proof) -> M r -> M r -> Proof
receivePLCDpres m p pPLCD m₁ m₂ =
    let p' = receive m p
    in  True
    === Deliver (pID p') m₁ `listElem` pHist p' -- restate a premise
    === Deliver (pID p') m₂ `listElem` pHist p' -- restate a premise
    === mVC m₁ `vcLess` mVC m₂ -- restate a premise
        ? receivePreservesIDandHist m p
    === Deliver (pID p) m₁ `listElem` pHist p -- establish precond of pPLCD
    === Deliver (pID p) m₂ `listElem` pHist p -- establish precond of pPLCD
        ? pPLCD m₁ m₂ -- generate evidence
    === processOrder (pHist p) (Deliver (pID p) m₁) (Deliver (pID p) m₂) -- restate generated evidence
    === processOrder (pHist p') (Deliver (pID p') m₁) (Deliver (pID p') m₂) -- restate conclusion
    *** QED
    --- NOTE: can comment out all of the equivalences here

-- *** deliver

{-@
type PLCDpreservation' r N OP
    =  p:Psized r {N}
    -> ClockHistoryAgreement {p}
    -> PLCD r {p}
    -> PLCD r {OP p}
@-}

cons :: a -> [a] -> [a]
cons x xs = x:xs
{-@ inline cons @-}

{-@
extendElem
    :: e:_
    -> {xs:_ | listElem e xs}
    -> w:_
    -> {listElem e (cons w xs)}
@-}
extendElem :: Eq a => a -> [a] -> a -> Proof
extendElem e [] _w      =   impossible
    {-restate premise-} $   listElem e []
extendElem e xs w
    {-restate conclusion-}  =   listElem e (w:xs)
    {-by def of listElem-}  === (e==w || listElem e xs)
    {-restate premise-}     === listElem e xs
                            *** QED

{-@
truncateElemTail4Head
    :: e:_
    -> h:_
    -> {xxs:_ | listElem e (listTailForHead h xxs) }
    -> { listElem e xxs }
@-}
truncateElemTail4Head :: Eq a => a -> a -> [a] -> Proof
truncateElemTail4Head e h []        =   impossible
    {-restate premise-}             $   listElem e (listTailForHead h [])
    {-by def of listTailForHead-}   === listElem e []
truncateElemTail4Head e h (x:xs)
    | h == x
        {-restate premise-}             =   listElem e (listTailForHead h (x:xs))
        {-by def of listTailForHead-}   === listElem e (if h==x then xs else listTailForHead h xs)
        {-simplify IfThenElse-}         === listElem e xs
        ? extendElem e xs x             === listElem e (x:xs)
                                        *** QED
    | otherwise
        {-restate premise-}             =   listElem e (listTailForHead h (x:xs))
        {-by def of listTailForHead-}   === listElem e (if h==x then xs else listTailForHead h xs)
        {-simplify IfThenElse-}         === listElem e (listTailForHead h xs)
        ? truncateElemTail4Head e h xs  === listElem e xs
        ? extendElem e xs x             === listElem e (x:xs)
                                        *** QED

{-@
extendElemTail4Head
    :: e:_
    -> h:_
    -> {xs:_ | listElem e (listTailForHead h xs) }
    -> w:_
    -> { listElem e (listTailForHead h (cons w xs)) }
@-}
extendElemTail4Head :: Eq a => a -> a -> [a] -> a -> Proof
extendElemTail4Head e h [] _w       =   impossible
    {-restate premise-}             $   listElem e (listTailForHead h [])
    {-by def of listTailForHead-}   === listElem e []
extendElemTail4Head e h xs w -- by cases of listTailForHead
    | h == w
        {-restate conclusion-}          =   listElem e (listTailForHead h (w:xs))
        {-by def of listTailForHead-}   === listElem e (if h==w then xs else listTailForHead h xs)
        {-simplify IfThenElse-}         === listElem e xs
        ? truncateElemTail4Head e h xs  *** QED
    | otherwise
        {-restate conclusion-}          =   listElem e (listTailForHead h (w:xs))
        {-by def of listTailForhead-}   === listElem e (if h==w then xs else listTailForHead h xs)
        {-simplify IfThenElse-}         === listElem e (listTailForHead h xs)
                                        *** QED

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

-- {-@ ple deliverPLCDpres_lemma1 @-}
{-@
deliverPLCDpres_lemma1
    :: n:Nat
    -> p:Psized r {n}
    -> ClockHistoryAgreement {p}
    -> PLCD r {p}
    -> {p':Psized r {n} | isJust (deliver p)
                        && p' == snd (fromJust (deliver p)) }
    -> {m1:Msized r {n} | listElem (Deliver (pID p') m1) (pHist p')
                        && m1 == fst (fromJust (deliver p)) }
    -> {m2:Msized r {n} | listElem (Deliver (pID p') m2) (pHist p')
                        && vcLess (mVC m1) (mVC m2) }
    -> { processOrder (pHist p') (Deliver (pID p') m1) (Deliver (pID p') m2) }
@-}
deliverPLCDpres_lemma1 :: Eq r => Int -> P r -> Proof -> (M r -> M r -> Proof) -> P r -> M r -> M r -> Proof
deliverPLCDpres_lemma1 n p pCHA pPLCD p' m₁ m₂ =
        ()
    *** Admit

{-@
deliverPLCDpres_lemma2
    :: n:Nat
    -> p:Psized r {n}
    -> ClockHistoryAgreement {p}
    -> PLCD r {p}
    -> {p':Psized r {n} | isJust (deliver p)
                        && p' == snd (fromJust (deliver p)) }
    -> {m1:Msized r {n} | listElem (Deliver (pID p') m1) (pHist p') }
    -> {m2:Msized r {n} | listElem (Deliver (pID p') m2) (pHist p')
                        && vcLess (mVC m1) (mVC m2)
                        && m2 == fst (fromJust (deliver p)) }
    -> { processOrder (pHist p') (Deliver (pID p') m1) (Deliver (pID p') m2) }
@-}
deliverPLCDpres_lemma2 :: Eq r => Int -> P r -> Proof -> (M r -> M r -> Proof) -> P r -> M r -> M r -> Proof
deliverPLCDpres_lemma2 n p pCHA pPLCD p' m₁ m₂ =
    let
    e₁  =   Deliver (pID p) m₁
        === Deliver (pID p) (coerce m₁)
    e₂  =   Deliver (pID p) m₂
        === Deliver (pID p) (coerce m₂)
    deliverBody
        =   deliver p
        === case dequeue (pVC p) (pDQ p) of
              Just (m, pDQ') -> Just (m, p
                { pVC = vcCombine (pVC p) (mVC m)
                , pDQ = pDQ'
                , pHist = Deliver (pID p) (coerce m) : pHist p
                }) -- by def of deliver
    p'VC
        =   pVC p' ? deliverBody
        === vcCombine (pVC p) (mVC m₂)
    p'Hist
        =   pHist p' ? deliverBody
        === e₂ : pHist p
    e₁inTail =
        {-restate a premise-}       e₁ `listElem` pHist p'
        ? p'Hist                === e₁ `listElem` (e₂ : pHist p)
        {-by def of listElem-}  === (e₁==e₂ || e₁ `listElem` pHist p)
        ? mVC m₁`vcLess`mVC m₂  === e₁ `listElem` pHist p
    in
                                True
    ? e₁inTail                  === e₁ `listElem` listTailForHead e₂ (pHist p')
    {-by def of processOrder-}  === processOrder (pHist p') e₁ e₂
                                *** QED

{-@
deliverPLCDpres_lemma3
    :: n:Nat
    -> p:Psized r {n}
    -> ClockHistoryAgreement {p}
    -> PLCD r {p}
    -> {p':Psized r {n} | isJust (deliver p)
                        && p' == snd (fromJust (deliver p)) }
    -> {m1:M r          | listElem (Deliver (pID p') m1) (pHist p') }
    -> {m2:MasM r {m1}  | listElem (Deliver (pID p') m2) (pHist p')
                        && vcLess (mVC m1) (mVC m2) }
    -> { m:Msized r {n} | m == fst (fromJust (deliver p))
                        && m /= m1
                        && m /= m2 }
    -> { processOrder (pHist p') (Deliver (pID p') m1) (Deliver (pID p') m2) }
@-}
deliverPLCDpres_lemma3 :: Eq r => Int -> P r -> Proof -> (M r -> M r -> Proof) -> P r -> M r -> M r -> M r -> Proof
deliverPLCDpres_lemma3 _n p _pCHA pPLCD p' m₁ m₂ m =
    let
    e₁  =   Deliver (pID p) m₁
        === Deliver (pID p) (coerce m₁)
    e₂  =   Deliver (pID p) m₂
        === Deliver (pID p) (coerce m₂)
    e₃  =   Deliver (pID p) m
        === Deliver (pID p) (coerce m)
    deliverBody
        =   deliver p
        === case dequeue (pVC p) (pDQ p) of
              Just (m, pDQ') -> Just (m, p
                { pVC = vcCombine (pVC p) (mVC m)
                , pDQ = pDQ'
                , pHist = Deliver (pID p) (coerce m) : pHist p
                }) -- by def of deliver
    p'VC
        =   pVC p' ? deliverBody
        === vcCombine (pVC p) (mVC m)
    p'Hist
        =   pHist p' ? deliverBody
        === e₃ : pHist p
    e₁inTail =
        {-restate a premise-}       e₁ `listElem` pHist p'
        ? p'Hist                === e₁ `listElem` (e₃ : pHist p)
        {-by def of listElem-}  === (e₁==e₃ || e₁ `listElem` pHist p)
        ? m₁ /= m               === e₁ `listElem` pHist p
    e₂inTail =
        {-restate a premise-}       e₂ `listElem` pHist p'
        ? p'Hist                === e₂ `listElem` (e₃ : pHist p)
        {-by def of listElem-}  === (e₂==e₃ || e₂ `listElem` pHist p)
        ? m₂ /= m               === e₂ `listElem` pHist p
    in
                                                True
    ? e₁inTail ? e₂inTail ? pPLCD m₁ m₂     === processOrder (pHist p) e₁ e₂
    ? extendProcessOrder (pHist p) e₁ e₂ e₃ === processOrder (e₃:pHist p) e₁ e₂
    ? p'Hist                                === processOrder (pHist p') e₁ e₂
                                            *** QED

{-@ ple deliverPLCDpres @-}
{-@
deliverPLCDpres :: n:Nat -> PLCDpreservation' r {n} {deliverShim} @-}
deliverPLCDpres :: Eq r => Int -> P r -> Proof -> (M r -> M r -> Proof) -> M r -> M r -> Proof
deliverPLCDpres n p pCHA pPLCD m₁ m₂ =
    case dequeue (pVC p) (pDQ p) of -- by cases of deliver
        Nothing -> pPLCD m₁ m₂ -- p is unchanged
----    Nothing -> -- p is unchanged
----        let p' = deliverShim p in
----            True
----        === Deliver (pID p') m₁ `listElem` pHist p' -- restate a premise
----        === Deliver (pID p') m₂ `listElem` pHist p' -- restate a premise
----        === mVC m₁ `vcLess` mVC m₂ -- restate a premise
----            ? (pID p' === pID p)
----            ? (pHist p' === pHist p)
----        === Deliver (pID p) m₁ `listElem` pHist p -- establish precond of pPLCD
----        === Deliver (pID p) m₂ `listElem` pHist p -- establish precond of pPLCD
----            ? pPLCD m₁ m₂
----        *** QED
        Just (m, pDQ') -- p delivered m and became (deliverShim p)
            -- by cases on the identity of m
            | m == m₁            -> deliverPLCDpres_lemma1 n p pCHA pPLCD (deliverShim p) m₁ m₂
            | m == m₂            -> deliverPLCDpres_lemma2 n p pCHA pPLCD (deliverShim p) m₁ m₂
            | m /= m₁ && m /= m₂ -> deliverPLCDpres_lemma3 n p pCHA pPLCD (deliverShim p) m₁ m₂ m


-- broadcast PLCD pres -- need CHA!



-- PLCD says
--
-- vc(m) < vc(m') => deliver(m) in-hist-prior-to deliver(m')
--
-- why is this true?  it's true because
--
-- * receive doesn't change history
-- * broadcastCycle calls deliver, and it's true for deliver
-- * deliver has two cases:
--      * deliver doesn't change history
--      * deliver does change history
--          * for own messages, it's truth doesn't change
--          * for other's messages:
--              * it's true because of how we choose whether to deliver
--              * we choose whether to deliver by making sure that the message
--                is the "next" one for the sender
--              * supremum of VCs in hist must be less-equal to pVC

-- (backburner) PLCDImpliesCD
-- (backburner) VCISO: cbcast implies vc-hb-copacetic
-- (NEXT!)      CBCAST observes PLCD
-- (backburner) CBCAST observes CD
