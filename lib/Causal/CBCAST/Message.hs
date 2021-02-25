{-# OPTIONS_GHC "-Wno-unused-imports" #-} -- FIXME: remove this after we can delete the ProofCombinators import

-- | Indirection module
module Causal.CBCAST.Message
( module X
, module Causal.CBCAST.Message
) where

import Causal.CBCAST.Verification as X
    (
--  -- * Vector clocks
--    Clock
--  , VC
--  , PID
--  , vcReadK, (!)
--  , vcLessEqualK
--  , vcLessK

    -- * Messages and operations
      Msg
--  , causallyBeforeK, CausallyBeforeProp
--  , vectorClocksConsistentWithCausalityProof
--  , causallyBeforeKvcLessKAliasProof

    -- * Processes and operations
    , Proc(pTime)
--  , deliverableK, DeliverableProp

--  -- * Safety proof
--  , processOrderAxiom
--  , safetyProof

    -- * Implementations over all K
    , andAtEachK        -- Required by LH
--  , vcLessEqual
--  , vcLess
    , causallyBefore
    , deliverableImpl

--  -- * Additional vector clock functions
--  , vcIndependent
--  , vcSize
--  , vcNew
--  , vcTick
--  , vcCombine
    )

import Language.Haskell.Liquid.ProofCombinators -- FIXME: LH is unhappy without this
import Causal.CBCAST.Verification as Internal

{-@
data Message r = Message { mMsg :: Msg, mRaw :: r } @-}
data Message r = Message { mMsg :: Msg, mRaw :: r }

{-@ measure mSender @-}
mSender :: Message r -> PID
mSender Message{mMsg=Msg{Internal.mSender=pid}} = pid

{-@ measure mSent @-}
mSent :: Message r -> VC
mSent Message{mMsg=Msg{Internal.mSent=vc}} = vc

{-@ reflect deliverable @-}
{-@
deliverable :: Proc -> Message r -> Bool @-}
deliverable :: Proc -> Message r -> Bool
deliverable p m = Internal.deliverableImpl (mMsg m) p
