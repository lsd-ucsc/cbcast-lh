
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
pEmptyCHA n p_id =
    let p = pEmpty n p_id in
        pHistVC p `vcLessEqual` pVC p -- restate conclusion
    === vcEmpty n `vcLessEqual` vcEmpty n -- by def of pEmpty,pHistVC,pHistVCHelper
        ? vcLessEqualReflexive (vcEmpty n)
    *** QED




-- * Hist VC

{-@
eventMessage :: n:Nat -> Event (VCMMsized {n}) r -> Msized r {n} @-}
eventMessage :: Int -> Event VCMM r -> M r
eventMessage _n (Broadcast (Message a b)) = Message a b
eventMessage _n (Deliver _pid (Message a b)) = Message a b
{-@ reflect eventMessage @-}

{-@
pHistVCHelper :: n:Nat -> Hsized r {n} -> VCsized {n} @-}
pHistVCHelper :: Int -> H r -> VC
pHistVCHelper n [] = vcEmpty n
pHistVCHelper n (Broadcast{}:es) = pHistVCHelper n es
pHistVCHelper n (e@Deliver{}:es) = mVC (eventMessage n e) `vcCombine` pHistVCHelper n es
{-@ reflect pHistVCHelper @-}

-- | The supremum of vector clocks on delivered messages in a process history.
{-@
pHistVC :: p:P r -> VCasP {p} @-}
pHistVC :: P r -> VC
pHistVC p = pHistVCHelper (listLength (pVC p)) (pHist p)
{-@ reflect pHistVC @-}
