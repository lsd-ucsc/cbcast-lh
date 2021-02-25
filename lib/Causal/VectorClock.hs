{-# OPTIONS_GHC "-Wno-unused-imports" #-} -- FIXME: remove this after we can delete the ProofCombinators import

-- | Indirection module
module Causal.VectorClock
( module X
) where

import Causal.CBCAST.Verification as X
    (
    -- * Vector clocks
      Clock
    , VC
    , PID
    , vcReadK, (!)
    , vcLessEqualK      -- Required by LH
    , vcLessK           -- Required by LH

--  -- * Messages and operations
--  , Msg
--  , causallyBeforeK, CausallyBeforeProp
--  , vectorClocksConsistentWithCausalityProof
--  , causallyBeforeKvcLessKAliasProof

--  -- * Processes and operations
--  , Proc
--  , deliverableK, DeliverableProp

--  -- * Safety proof
--  , processOrderAxiom
--  , safetyProof

    -- * Implementations over all K
    , andAtEachK        -- Required by LH
    , vcLessEqual
    , vcLess
--  , causallyBefore
--  , deliverable

    -- * Additional vector clock functions
    , vcIndependent
    , vcSize
    , vcNew
    , vcTick
    , vcCombine
    )

import Language.Haskell.Liquid.ProofCombinators -- FIXME: LH is unhappy without this
