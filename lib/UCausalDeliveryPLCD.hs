{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}
{-# OPTIONS_GHC "-Wno-unused-imports" #-} -- LH needs Redefined.Ord
module UCausalDeliveryPLCD where

import Language.Haskell.Liquid.ProofCombinators
import Redefined.Fin
import Redefined.Ord
import Redefined.Proof (proofConst)

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

{-@
eventN :: Event VCMM r -> Nat @-}
eventN :: Event VCMM r -> Int
eventN (Broadcast m) = listLength (mVC m)
eventN (Deliver _pid m) = listLength (mVC m)
{-@ inline eventN @-} -- Required so that eventVC's annotation passes.

-- | The vc for the message in an event.
{-@
eventVC :: e:Event VCMM r -> VCsized {eventN e} @-}
eventVC :: Event VCMM r -> VC
eventVC (Broadcast m) = mVC m
eventVC (Deliver _pid m) = mVC m
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
pHistVCHelper n (e:es) = (eventVC e `proofConst` vcmmSizedEventVC n e) `vcCombine` pHistVCHelper n es
{-@ reflect pHistVCHelper @-}

{-@ ple vcmmSizedEventVC @-}
{-@
vcmmSizedEventVC :: n:Nat -> e:Event (VCMMsized {n}) r -> { n == len (eventVC e) } @-}
vcmmSizedEventVC :: Int -> Event VCMM r -> Proof
vcmmSizedEventVC _n (Broadcast    m) = mVC m === vcmmSent (mMetadata m) *** QED
vcmmSizedEventVC _n (Deliver _pid m) = mVC m === vcmmSent (mMetadata m) *** QED

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
            === vcCombine (eventVC e) (pHistVCHelper n (pHist p₁)) -- by def of pHistVCHelper
                ? (eventVC e === mVC m)
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

{-@ ple vcCombineIdempotence @-}
{-@
vcCombineIdempotence :: a:VC -> {a == vcCombine a a} @-}
vcCombineIdempotence :: VC -> Proof
vcCombineIdempotence [] = ()
vcCombineIdempotence (_x:xs) = vcCombineIdempotence xs

-- TODO: also use this lemma up above to shorten deliverHistVcIsPrevCombineMsg
{-@ ple pHistVC_unfoldStep @-}
{-@
pHistVC_unfoldStep
    ::   n:Nat
    ->  p0:Psized r {n}
    ->   m:Msized r {n}
    -> { e:Event (VCMMsized {n}) r | e == Broadcast m
                                  || e == Deliver (pID p0) m }
    -> {p1:Psized r {n} | pHist p1 == cons e (pHist p0) }
    -> { pHistVC p1 == vcCombine (pHistVC p0) (mVC m) }
@-}
pHistVC_unfoldStep :: Int -> P r -> M r -> Event VCMM r -> P r -> Proof
pHistVC_unfoldStep n p₀ m e p₁ =
    let
    e_vc
        =   eventVC e
        === mVC m -- by def of eventVC, but requires PLE for some reason
    p₀histVC
                                        =   pHistVC p₀
        ? (n === listLength (pVC p₀))   === pHistVCHelper n (pHist p₀) -- by def of pHistVC, but requires PLE for some reason
    in
    {-restate (part of) conclusion-}    pHistVC p₁
    ? (n === listLength (pVC p₁))   === pHistVCHelper n (pHist p₁) -- by def of pHistVC, but requires PLE for some reason
    {-by premise-}                  === pHistVCHelper n (e : pHist p₀)
    {-by def of pHistVCHelper-}     === (eventVC e `proofConst` vcmmSizedEventVC n e) `vcCombine` pHistVCHelper n (pHist p₀)
    {-simplify-}                    === eventVC e `vcCombine` pHistVCHelper n (pHist p₀)
    ? p₀histVC                      === eventVC e `vcCombine` pHistVC p₀
    ? e_vc                          === mVC m `vcCombine` pHistVC p₀
    ? vcCombineCommutativity n (mVC m) (pHistVC p₀)
    {-restate (part of) conclusion-}=== pHistVC p₀ `vcCombine` mVC m
                                    *** QED

{-@
broadcastCHApres :: raw:r -> n:Nat -> CHApreservation r {n} {broadcastShim raw} @-}
broadcastCHApres :: r -> Int -> P r -> Proof -> Proof
broadcastCHApres raw n p₀ _pCHA =
    let
    -- inject new message into p₀ to obtain p₁
    m = broadcastHelper_prepareMessage raw p₀
    e = Broadcast (coerce m)
    --      ? (coerce m === m)
    --  === Broadcast m -- QQQ: Why does adding this extra information break the proof?
    p₁
                                                    =   broadcastHelper_injectMessage m p₀
        {-by def of broadcastHelper_injectMessage-} === P (pVC p₀) (pID p₀) (m : pDQ p₀) (e : pHist p₀)
    p₁vc
                                                    =   pVC p₁
        {-by def of broadcastHelper_injectMessage-} === pVC p₀
    p₁histVC
                                                =   pHistVC p₁
        ? pHistVC_unfoldStep n p₀ m e p₁        === vcCombine (pHistVC p₀) (mVC m)

    -- deliver from p₁ to obtain p₂
    Just (_m, p₂) = deliver p₁ ? broadcastAlwaysDelivers raw p₀
    p₂vc
                                                =   pVC p₂
        ? deliverVcIsPrevCombineMsg p₁ m p₂     === vcCombine (pVC p₁) (mVC m)
    p₂histVC
                                                =   pHistVC p₂
        ? deliverHistVcIsPrevCombineMsg p₁ m p₂ === vcCombine (pHistVC p₁) (mVC m)
    in
                                                vcLessEqual (pHistVC p₂) (pVC p₂) -- restate conclusion
    ? p₂histVC ? p₂vc                       === vcLessEqual (pHistVC p₁ `vcCombine` mVC m) (pVC p₁ `vcCombine` mVC m)
    ? p₁histVC ? p₁vc                       === vcLessEqual (pHistVC p₀ `vcCombine` mVC m `vcCombine` mVC m) (pVC p₀ `vcCombine` mVC m)
    ? vcCombineAssociativity n
        (pHistVC p₀) (mVC m) (mVC m)        === vcLessEqual (pHistVC p₀ `vcCombine` (mVC m `vcCombine` mVC m)) (pVC p₀ `vcCombine` mVC m)
    ? vcCombineIdempotence (mVC m)          === vcLessEqual (pHistVC p₀ `vcCombine` mVC m) (pVC p₀ `vcCombine` mVC m)
    ? vcCombineVCLessEqualMonotonicLeft n
        (pHistVC p₀) (pVC p₀) (mVC m)       === vcLessEqual (pHistVC p₀) (pVC p₀) -- restate premise
                                            *** QED




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

{-@
deliverableImpliesNotVCLessEqual_lemma
    ::  lb:Nat
    -> {ub:Nat | lb <= ub}
    -> {m_sender:PIDsized {ub} | lb <= m_sender}
    -> m_vc:VCsized {ub-lb}
    -> p_vc:VCsized {ub-lb}
    -> { not ( listAnd (listZipWith3 (deliverableHelper m_sender) (finAscHelper lb ub) m_vc p_vc)
            && listAnd (listZipWith vcLessEqualHelper m_vc p_vc) ) }
@-}
deliverableImpliesNotVCLessEqual_lemma :: Int -> Int -> PID -> VC -> VC -> Proof
deliverableImpliesNotVCLessEqual_lemma lb ub m_sender (m_vc_k:m_vc) (p_vc_k:p_vc)
    -- by cases of deliverableHelper
    | lb == m_sender
        {-restate conclusion-}          =   not (listAnd (listZipWith3 (deliverableHelper m_sender) (finAscHelper lb ub) (m_vc_k:m_vc) (p_vc_k:p_vc)) && listAnd (listZipWith vcLessEqualHelper (m_vc_k:m_vc) (p_vc_k:p_vc)))
        {-by def of finAscHelper-}      === not (listAnd (listZipWith3 (deliverableHelper m_sender) (lb:finAscHelper (lb+1) ub) (m_vc_k:m_vc) (p_vc_k:p_vc)) && listAnd (listZipWith vcLessEqualHelper (m_vc_k:m_vc) (p_vc_k:p_vc)))
        {-by def of zipWith3,zipWith-}  === not (listAnd (deliverableHelper m_sender lb m_vc_k p_vc_k : listZipWith3 (deliverableHelper m_sender) (finAscHelper (lb+1) ub) (m_vc) (p_vc)) && listAnd (vcLessEqualHelper m_vc_k p_vc_k : listZipWith vcLessEqualHelper m_vc p_vc))
        {-by def of listAnd-}           === not (deliverableHelper m_sender lb m_vc_k p_vc_k && listAnd (listZipWith3 (deliverableHelper m_sender) (finAscHelper (lb+1) ub) (m_vc) (p_vc)) && vcLessEqualHelper m_vc_k p_vc_k && listAnd (listZipWith vcLessEqualHelper m_vc p_vc))
        {-∀a,b.¬(a∧b)⇔(¬a∨¬b)-}         === not (deliverableHelper m_sender lb m_vc_k p_vc_k && vcLessEqualHelper m_vc_k p_vc_k)
        {-by defs of helpers-}          === not (m_vc_k == p_vc_k + 1 && m_vc_k <= p_vc_k)
        *** QED
    | lb < m_sender
        {-restate conclusion-}          =   not (listAnd (listZipWith3 (deliverableHelper m_sender) (finAscHelper lb ub) (m_vc_k:m_vc) (p_vc_k:p_vc)) && listAnd (listZipWith vcLessEqualHelper (m_vc_k:m_vc) (p_vc_k:p_vc)))
        {-by def of finAscHelper-}      === not (listAnd (listZipWith3 (deliverableHelper m_sender) (lb:finAscHelper (lb+1) ub) (m_vc_k:m_vc) (p_vc_k:p_vc)) && listAnd (listZipWith vcLessEqualHelper (m_vc_k:m_vc) (p_vc_k:p_vc)))
        {-by def of zipWith3,zipWith-}  === not (listAnd (deliverableHelper m_sender lb m_vc_k p_vc_k : listZipWith3 (deliverableHelper m_sender) (finAscHelper (lb+1) ub) (m_vc) (p_vc)) && listAnd (vcLessEqualHelper m_vc_k p_vc_k : listZipWith vcLessEqualHelper m_vc p_vc))
        {-by def of listAnd-}           === not (deliverableHelper m_sender lb m_vc_k p_vc_k && listAnd (listZipWith3 (deliverableHelper m_sender) (finAscHelper (lb+1) ub) (m_vc) (p_vc)) && vcLessEqualHelper m_vc_k p_vc_k && listAnd (listZipWith vcLessEqualHelper m_vc p_vc))
        {-associativity of ∧-}          === not (deliverableHelper m_sender lb m_vc_k p_vc_k && vcLessEqualHelper m_vc_k p_vc_k
                                                && listAnd (listZipWith3 (deliverableHelper m_sender) (finAscHelper (lb+1) ub) (m_vc) (p_vc)) && listAnd (listZipWith vcLessEqualHelper m_vc p_vc))
        ? deliverableImpliesNotVCLessEqual_lemma (lb+1) ub m_sender m_vc p_vc
                                        === not (deliverableHelper m_sender lb m_vc_k p_vc_k && vcLessEqualHelper m_vc_k p_vc_k && False)
        *** QED

{-@
deliverableImpliesNotVCLessEqual
    :: m:M r
    -> { p_vc:VCasM {m} | deliverable m p_vc }
    -> { not (vcLessEqual (mVC m) p_vc) }
@-}
deliverableImpliesNotVCLessEqual :: M r -> VC -> Proof
deliverableImpliesNotVCLessEqual m p_vc =
                            let n = listLength p_vc in
    {-restate theorem-}         (if deliverable m p_vc then not (vcLessEqual (mVC m) p_vc) else True)
    {-∀a,b.(a⇒b)⇔(¬a∨b)-}   === (not (deliverable m p_vc) || not (vcLessEqual (mVC m) p_vc))
    {-∀a,b.¬(a∧b)⇔(¬a∨¬b)-} === not (deliverable m p_vc && vcLessEqual (mVC m) p_vc)
    {-by def of deliverable,vcLessEqual-}
                            === not ( listAnd (listZipWith3 (deliverableHelper (mSender m)) (finAsc n) (mVC m) p_vc)
                                   && listAnd (listZipWith vcLessEqualHelper (mVC m) p_vc) )
    ? deliverableImpliesNotVCLessEqual_lemma 0 n (mSender m) (mVC m) p_vc
                            === True
                            *** QED

{-@
dequeueImpliesDeliverable
    :: vc:VC
    -> {dq:DQasV r {vc} | isJust (dequeue vc dq)}
    -> {deliverable (fst (fromJust (dequeue vc dq))) vc}
@-}
dequeueImpliesDeliverable :: VC -> DQ r -> Proof
dequeueImpliesDeliverable vc [] =   impossible
    {-restate premise-}         $   dequeue vc []
    {-by def of dequeue-}       === Nothing
dequeueImpliesDeliverable vc (x:xs)
    | deliverable x vc =
        {-restate premise-}         dequeue vc (x:xs)
        {-by def of deliverable-}   === Just (x, xs)
        {-by case assumption-}      *** QED
    | otherwise =
        case dequeue vc xs of
            Nothing ->                          impossible
                {-restate premise-}         $   dequeue vc (x:xs)
                {-by def of deliverable-}   === Nothing
            Just (m, xs') ->
                {-restate premise-}                 dequeue vc (x:xs)
                {-by def of deliverable-}           === Just (m, x:xs')
                ? dequeueImpliesDeliverable vc xs   *** QED

{-@
deliverImpliesDeliverable
    :: {p:P r | isJust (deliver p)}
    -> {deliverable (fst (fromJust (deliver p))) (pVC p)}
@-}
deliverImpliesDeliverable :: P r -> Proof
deliverImpliesDeliverable p =
    case dequeue (pVC p) (pDQ p) of
        Nothing ->                      impossible
            {-restate premise-}     $   deliver p
            {-by def of deliver-}   === Nothing
        Just (m, pDQ') ->
            {-restate premise-}     deliver p
            {-by def of deliver-}   === Just (m, p
                                            { pVC = vcCombine (pVC p) (mVC m)
                                            , pDQ = pDQ'
                                            , pHist = Deliver (pID p) (coerce m) : pHist p
                                            })
            ? dequeueImpliesDeliverable (pVC p) (pDQ p)
                                    *** QED

{-@ ple vcCombineResultLarger @-}
{-@
vcCombineResultLarger :: a:VC -> b:VCasV {a} -> { vcLessEqual a (vcCombine a b)
                                               && vcLessEqual b (vcCombine a b) } @-}
vcCombineResultLarger :: VC -> VC -> Proof
vcCombineResultLarger [] []
    {-restate conclusion-}      =   vcCombine [] []
    {-by def of vcCombine-}     === listZipWith ordMax [] []
    {-by def of listZipWith-}   === []
    ? vcLessEqualReflexive []   *** QED
vcCombineResultLarger (x:xs) (y:ys)
    {-restate (half of) conclusion-}    =   vcLessEqual (x:xs) ret
    {-by def of listAnd,zipWith,etc-}   === (x <= (if x < y then y else x) && listAnd (listZipWith vcLessEqualHelper xs (vcCombine xs ys)))
    ? vcCombineResultLarger xs ys       === (x <= (if x < y then y else x))
    {-vcCombineAssociativity-}          *** QED
  where
    ret =   vcCombine (x:xs) (y:ys)
        === listZipWith ordMax (x:xs) (y:ys)
        === ordMax x y : listZipWith ordMax xs ys
        === (if x < y then y else x) : listZipWith ordMax xs ys

{-@ ple histElemLessEqualHistVC_lemma @-} -- Required to see through eventVC and pHistVC definitions.
{-@
histElemLessEqualHistVC_lemma :: e:Event VCMM r -> {hhs:Hsized r {eventN e} | listElem e hhs} -> {vcLessEqual (eventVC e) (pHistVCHelper (eventN e) hhs)} @-}
histElemLessEqualHistVC_lemma :: Eq r => Event VCMM r -> H r -> Proof
histElemLessEqualHistVC_lemma e []  =   impossible
                                    $   listElem e []
histElemLessEqualHistVC_lemma e (h:hs)
  | e == h                              =   True
    ? vcCombineResultLarger eVC hsVC    === eVC `vcLessEqual` hhsVC
                                        *** QED
  | otherwise =
                                                    True
    ? histElemLessEqualHistVC_lemma e hs        === eVC `vcLessEqual` hsVC
    ? vcCombineResultLarger (eventVC h) hsVC    === hsVC `vcLessEqual` hhsVC
    ? vcLessEqualTransitive n eVC hsVC hhsVC    === eVC `vcLessEqual` hhsVC
                                                *** QED
  where
    n = eventN e
    eVC = eventVC e
    hsVC = pHistVCHelper n hs
    hhsVC = pHistVCHelper n (h:hs)
        === (eventVC h `proofConst` vcmmSizedEventVC n h) `vcCombine` hsVC

{-@ ple histElemLessEqualHistVC @-} -- Required to see through eventVC and pHistVC definitions.
{-@
histElemLessEqualHistVC :: e:Event VCMM r -> {p:Psized r {eventN e} | listElem e (pHist p)} -> {vcLessEqual (eventVC e) (pHistVC p)} @-}
histElemLessEqualHistVC :: Eq r => Event VCMM r -> P r -> Proof
histElemLessEqualHistVC e p =
        eventVC e `vcLessEqual` pHistVC p
    === eventVC e `vcLessEqual` pHistVCHelper (listLength (pVC p)) (pHist p)
    === eventVC e `vcLessEqual` pHistVCHelper (eventN e) (pHist p)
        ? histElemLessEqualHistVC_lemma e (pHist p)
    *** QED

{-@
mVCEqualsEventVC :: p_id:PID -> m:M r -> { mVC m == eventVC (Deliver p_id m) } @-}
mVCEqualsEventVC :: PID -> M r -> Proof
mVCEqualsEventVC p_id m = mVC m === eventVC (Deliver p_id m) *** QED
-- QQQ: Why is this lemma required?

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
deliverPLCDpres_lemma1 n p pCHA _pPLCD p' m₁ m₂ =
    let
    e₁  =   Deliver (pID p) (coerce m₁)
        === Deliver (pID p) m₁
    e₂  =   Deliver (pID p) (coerce m₂)
        === Deliver (pID p) m₂
    deliverBody
        =   deliver p
        === case dequeue (pVC p) (pDQ p) of
              Just (m, pDQ') -> Just (m, p
                { pVC = vcCombine (pVC p) (mVC m)
                , pDQ = pDQ'
                , pHist = Deliver (pID p) (coerce m) : pHist p
                }) -- by def of deliver
    p'Hist
        =   pHist p' ? deliverBody
        === e₁ : pHist p
    e₂inTail =
        {-restate a premise-}       e₂ `listElem` pHist p'
        ? p'Hist                === e₂ `listElem` (e₁ : pHist p)
        {-by def of listElem-}  === (e₂==e₁ || e₂ `listElem` pHist p)
        ? mVC m₁`vcLess`mVC m₂  === e₂ `listElem` pHist p
    m₁lessEqualpVC =
                                            True
        ? (mVC m₁ `vcLess` mVC m₂)      === mVC m₁ `vcLessEqual` mVC m₂
        ? mVCEqualsEventVC (pID p) m₂   === (mVC m₂ == eventVC e₂)
        ? e₂inTail ? histElemLessEqualHistVC e₂ p
                                        === eventVC e₂ `vcLessEqual` pHistVC p
        ? pCHA                          === pHistVC p `vcLessEqual` pVC p
        ? vcLessEqualTransitive n (mVC m₁) (eventVC e₂) (pHistVC p)
        ? vcLessEqualTransitive n (mVC m₁) (pHistVC p) (pVC p)
                                        === mVC m₁ `vcLessEqual` pVC p
                                        *** QED
    m₁notLessEqualpVC =
                                            True
        ? deliverImpliesDeliverable p   === deliverable m₁ (pVC p)
        ? deliverableImpliesNotVCLessEqual m₁ (pVC p)
                                        === not (mVC m₁ `vcLessEqual` pVC p)
                                        *** QED
    in
    impossible  $   m₁lessEqualpVC
                &&& m₁notLessEqualpVC

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
deliverPLCDpres_lemma2 _n p _pCHA _pPLCD p' m₁ m₂ =
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
              Just (m', pDQ') -> Just (m', p
                { pVC = vcCombine (pVC p) (mVC m')
                , pDQ = pDQ'
                , pHist = Deliver (pID p) (coerce m') : pHist p
                }) -- by def of deliver
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
        Just (m, _pDQ') -- p delivered m and became (deliverShim p)
            | m == m₁            -> deliverPLCDpres_lemma1 n p pCHA pPLCD (deliverShim p) m₁ m₂
            | m == m₂            -> deliverPLCDpres_lemma2 n p pCHA pPLCD (deliverShim p) m₁ m₂
            | m /= m₁ && m /= m₂ -> deliverPLCDpres_lemma3 n p pCHA pPLCD (deliverShim p) m₁ m₂ m

-- *** broadcast


{-@
broadcastPreservesDeliveries
    :: raw:r
    ->  p :P r
    -> { m:M r | listElem (Deliver (pID (broadcastShim raw p)) m) (pHist (broadcastShim raw p)) }
    -> { listElem (Deliver (pID p) m) (pHist p) }
@-}
broadcastPreservesDeliveries :: r -> P r -> M r -> Proof
broadcastPreservesDeliveries _raw _p _m =

{-@
broadcastPLCDpres :: raw:r -> n:Nat -> PLCDpreservation' r {n} {broadcastShim raw} @-}
broadcastPLCDpres :: Eq r => r -> Int -> P r -> Proof -> (M r -> M r -> Proof) -> M r -> M r -> Proof
broadcastPLCDpres raw _n p _pCHA pPLCD m₁ m₂ =
    let
    e₁  =   Deliver (pID p) (coerce m₁)
    e₂  =   Deliver (pID p) (coerce m₂)

    -- inject new message into p to obtain p'
    m   =   broadcastHelper_prepareMessage raw p
    e'  =   Broadcast (coerce m)
    p'  =   broadcastHelper_injectMessage m p
        === P (pVC p) (pID p) (m : pDQ p) (e' : pHist p)
    p'id    =   pID p'
            === pID p
    p'hist  =   pHist p'
            === e' : pHist p

    -- deliver from p' to obtain p''
    Just (_m, p'')
        =   deliver p' ? broadcastAlwaysDelivers raw p
        === case dequeue (pVC p') (pDQ p') of
              Just (m', pDQ') -> Just (m', p'
                { pVC = vcCombine (pVC p') (mVC m')
                , pDQ = pDQ'
                , pHist = Deliver (pID p) (coerce m') : pHist p'
                }) -- by def of deliver
    e'' =   Deliver (pID p) (coerce m)
        === Deliver (pID p) m
    p''id   =   pID p''
            === pID p
    p''hist =   pHist p'' ? (m === _m)
            === e'' : pHist p'
    in
                                                        True
    ? broadcastPreservesDeliveries raw p m₁         === e₁ `listElem` pHist p
    ? broadcastPreservesDeliveries raw p m₂         === e₂ `listElem` pHist p
    ? pPLCD m₁ m₂                                   === processOrder (       pHist p) e₁ e₂
    ? extendProcessOrder (pHist p) e₁ e₂ e'         === processOrder (    e':pHist p) e₁ e₂
    ? extendProcessOrder (e' : pHist p) e₁ e₂ e''   === processOrder (e'':e':pHist p) e₁ e₂
    ? (pHist p'  === e' :pHist p)                   === processOrder (e'':   pHist p') e₁ e₂
    ? (pHist p'' === e'':pHist p') ? (m === _m)     === processOrder (       pHist p'') e₁ e₂
