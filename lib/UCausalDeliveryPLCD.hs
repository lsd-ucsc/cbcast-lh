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




-- * Preservation property shims

-- | The deliver function, but throw away the message.
deliverShim :: P r -> P r
deliverShim p =
    case deliver p of
        Nothing -> p
        Just (_, p') -> p'
{-@ reflect deliverShim @-}

-- | The broadcast function, but throw away the message.
broadcastShim :: r -> P r -> P r
broadcastShim raw p =
    let (_, p') = broadcast raw p in p'
{-@ reflect broadcastShim @-}




-- * Preservation lemmas

{-@
receiveKeepsVC_noPLE :: m:M r -> p:PasM r {m} -> {pVC p == pVC (receive m p)} @-}
receiveKeepsVC_noPLE :: M r -> P r -> Proof
receiveKeepsVC_noPLE m p -- by cases from receive
    | mSender m == pID p
        =   pVC p == pVC (receive m p) -- restate conclusion
        === pVC p == pVC p -- by def of receive
        *** QED
    | otherwise
        =   pVC p == pVC (receive m p) -- restate conclusion
        === pVC p == pVC p{ pDQ = enqueue m (pDQ p) } -- by def of receive
        *** QED

{-@ ple receiveKeepsVC @-}
{-@
receiveKeepsVC :: m:M r -> p:PasM r {m} -> {pVC p == pVC (receive m p)} @-}
receiveKeepsVC :: M r -> P r -> Proof
receiveKeepsVC m p -- by cases from receive
    | mSender m == pID p = ()
    | otherwise
        =   p{ pDQ = enqueue m (pDQ p) } -- by def of receive
        *** QED

{-@ ple receiveKeepsHist @-}
{-@
receiveKeepsHist :: m:M r -> p:PasM r {m} -> {pHist p == pHist (receive m p)} @-}
receiveKeepsHist :: M r -> P r -> Proof
receiveKeepsHist m p -- by cases from receive
    | mSender m == pID p = ()
    | otherwise
        =   p{ pDQ = enqueue m (pDQ p) } -- by def of receive
        *** QED

{-@ ple receiveKeepsID @-}
{-@
receiveKeepsID :: m:M r -> p:PasM r {m} -> {pID p == pID (receive m p)} @-}
receiveKeepsID :: M r -> P r -> Proof
receiveKeepsID m p -- by cases from receive
    | mSender m == pID p = ()
    | otherwise
        =   p{ pDQ = enqueue m (pDQ p) } -- by def of receive
        *** QED




-- * Clock-History agreement

-- ** CHA utilities

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




-- ** CHA property

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

{-@
receiveCHApres_noPLE :: m:M r -> CHApreservation r {len (mVC m)} {receive m} @-}
receiveCHApres_noPLE :: M r -> P r -> Proof -> Proof
receiveCHApres_noPLE m p _pCHA
    =   let p' = receive m p in
        pHistVC p
        ? receiveKeepsVC m p
        ? receiveKeepsHist m p
    === pHistVC p'
    *** QED

{-@ ple receiveCHApres @-}
{-@
receiveCHApres :: m:M r -> CHApreservation r {len (mVC m)} {receive m} @-}
receiveCHApres :: M r -> P r -> Proof -> Proof
receiveCHApres m p _pCHA
    =   receiveKeepsVC m p
    &&& receiveKeepsHist m p

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
        Just (_m, pDQ') -> -- one case, due to premise
                p₂
            === p₁{ pVC = vcCombine (pVC p₁) (mVC m)
                  , pDQ = pDQ'
                  , pHist = Deliver (pID p₁) (coerce m) : pHist p₁
                  } -- by def of deliver
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
        Just (_m, pDQ') -> -- one case, due to premise
            let n = listLength (pVC p₁)
                e = Deliver (pID p₁) (coerce m)
            in  pHistVC p₂ -- restate (part of) conclusion
                ? (   p₂
                  === p₁{ pVC = vcCombine (pVC p₁) (mVC m)
                        , pDQ = pDQ'
                        , pHist = e : pHist p₁
                        } -- by def of deliver
                  ) -- lemma to help LH see through record-update-syntax
            === pHistVCHelper n (e : pHist p₁) -- by def of deliver,pHistVC
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
pEmptyPLCD n p_id m1 _m2 -- Interesting but unnecessary manual proof:
    =   True
    --- QQQ: Why doesn't this premise report as True without PLE?
    === listElem (Deliver p_id m1) (pHist (pEmpty n p_id)) -- restate a premise
    --- QQQ: Why doesn't expanding the definition of pEmpty work without PLE?
    === listElem (Deliver p_id m1) (pHist P{pVC=vcEmpty n, pID=p_id, pDQ=[], pHist=[]}) -- by def of pEmpty
    === listElem (Deliver p_id m1) [] -- by def of pHist
    === False -- by def of listElem
    *** QED -- premise failed
-- NOTE: can comment the whole proof
-- pEmptyPLCD _n _p_id _m1 _m2 = () -- Premises don't hold.




-- ** PLCD preservation

{-@
type PLCDpreservation r N OP
    =  p:Psized r {N}
    -> PLCD r {p}
    -> PLCD r {OP p}
@-}

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
        ? receiveKeepsID m p
        ? receiveKeepsHist m p
    === Deliver (pID p) m₁ `listElem` pHist p -- establish precond of pPLCD
    === Deliver (pID p) m₂ `listElem` pHist p -- establish precond of pPLCD
        ? pPLCD m₁ m₂ -- generate evidence
    === processOrder (pHist p) (Deliver (pID p) m₁) (Deliver (pID p) m₂) -- restate generated evidence
    === processOrder (pHist p') (Deliver (pID p') m₁) (Deliver (pID p') m₂) -- restate conclusion
    *** QED
    --- NOTE: can comment out all of the equivalences here

-- deliver PLCD pres -- need CHA!

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
