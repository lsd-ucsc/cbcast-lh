{-# OPTIONS_GHC "-Wno-unused-imports" #-} -- FIXME: remove this after we can delete the ProofCombinators import
{-# LANGUAGE NamedFieldPuns #-}

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
    , Proc(Proc, procId, procVc)
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
data Message r = Message { mSender::PID, mSent::VC, mRaw::r } @-}
data Message r = Message { mSender::PID, mSent::VC, mRaw::r }

-- | For calls into the Verification module's code.
{-@ measure mMsg @-}
mMsg :: Message r -> Msg
mMsg Message{mSender, mSent} = Msg{senderId=mSender, messageVc=mSent}

{-@ reflect deliverable @-}
{-@
deliverable :: Proc -> Message r -> Bool @-}
deliverable :: Proc -> Message r -> Bool
deliverable p m = Internal.deliverableImpl (mMsg m) p
