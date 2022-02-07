{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}
module UCausalDeliveryPLCD where

--{-@ LIQUID "--check-var=broadcast" @-}
--{-@ LIQUID "--check-var=broadcastHelper_prepareMessage" @-}
--{-@ LIQUID "--check-var=broadcastHelper_injectMessage" @-}
--{-@ LIQUID "--check-var=broadcastAlwaysDelivers" @-}
--
--{-@ LIQUID "--check-var=broadcastAlwaysDequeues" @-}
--{-@ LIQUID "--check-var=broadcastAlwaysDequeues_lemma" @-}
--
--{-@ LIQUID "--check-var=deliverableAlwaysDequeues" @-}
--{-@ LIQUID "--diff" @-}

import Language.Haskell.Liquid.ProofCombinators
import Redefined.Fin
import Redefined.Ord
-- import Redefined.Proof (proofConst)

import SystemModel
import Properties
import UCausalDelivery




-- * Clock-History agreement

-- ** CHA utilities

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
type CHApreservation r OP
    =  p:P r
    -> ClockHistoryAgreement {p}
    -> ClockHistoryAgreement {OP p}
@-}

{-@
receiveCHApres :: m:_ -> CHApreservation r {receive m} @-}
receiveCHApres :: M r -> P r -> Proof -> Proof
receiveCHApres _m _p _cha = () *** Admit




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
pEmptyPLCD _n _p_id _m1 _m2 = () -- Premises don't hold.
--pEmptyPLCD n p_id m1 _m2 -- Interesting but unnecessary manual proof:
--    =   True
--    --- QQQ: Why doesn't this premise report as True without PLE?
--    === listElem (Deliver p_id m1) (pHist (pEmpty n p_id)) -- restate a premise
--    --- QQQ: Why doesn't expanding the definition of pEmpty work without PLE?
--    === listElem (Deliver p_id m1) (pHist P{pVC=vcEmpty n, pID=p_id, pDQ=[], pHist=[]}) -- by def of pEmpty
--    === listElem (Deliver p_id m1) [] -- by def of pHist
--    === False -- by def of listElem
--    *** QED -- premise failed




-- ** PLCD preservation

{-@
type PLCDpreservation r OP
    =  p:P r
    -> PLCD r {p}
    -> PLCD r {OP p}
@-}

{-@
receivePLCDpres :: m:_ -> PLCDpreservation r {receive m} @-}
receivePLCDpres :: M r -> P r -> (M r -> M r -> Proof) -> M r -> M r -> Proof
receivePLCDpres _m _p _plcd _m1 _m2 = () *** Admit



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
