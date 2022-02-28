
-- | Clock-history agreement definition.
module UCausalDelivery_CHA where

import Language.Haskell.Liquid.ProofCombinators
import Redefined.Fin
import Redefined.Ord
import Redefined.Proof (proofConst)

import SystemModel
import Properties
import Properties2
import UCausalDelivery

{-@
type ClockHistoryAgreement P
    = {_ : Proof | vcLessEqual (pHistVC P) (pVC P) }
@-}

{-@
type CHApreservation r N OP
    =  p:Psized r {N}
    -> ClockHistoryAgreement {p}
    -> ClockHistoryAgreement {OP p}
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




-- * Hist VC

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
pHistVCHelper n (Broadcast{}:es) = pHistVCHelper n es
pHistVCHelper n (e@Deliver{}:es) = (eventVC e `proofConst` vcmmSizedEventVC n e) `vcCombine` pHistVCHelper n es
{-@ reflect pHistVCHelper @-}

{-@ ple vcmmSizedEventVC @-}
{-@
vcmmSizedEventVC :: n:Nat -> e:Event (VCMMsized {n}) r -> { n == len (eventVC e) } @-}
vcmmSizedEventVC :: Int -> Event VCMM r -> Proof
vcmmSizedEventVC _n (Broadcast    m) = mVC m === vcmmSent (mMetadata m) *** QED
vcmmSizedEventVC _n (Deliver _pid m) = mVC m === vcmmSent (mMetadata m) *** QED

