{-# OPTIONS_GHC "-Wno-orphans" #-} -- Clients need Show and Generic instances
{-# LANGUAGE StandaloneDeriving #-} -- Show instances of internal CBCAST types
{-# LANGUAGE DeriveGeneric #-} -- Generic instances of internal CBCAST types

{-@ LIQUID "--skip-module" @-}

-- | TODO: Move this back to lib/CBCAST.hs when the bug is fixed:
-- https://github.com/ucsd-progsys/liquidhaskell/issues/2019
module CBCAST.Generic where

import GHC.Generics (Generic)

import qualified CBCAST.Core as CB

deriving instance Generic r => Generic (CB.Process r)
deriving instance Generic r => Generic (CB.Message r)
deriving instance Generic r => Generic (CB.Event r)

deriving instance Show r => Show (CB.Process r)
deriving instance Show r => Show (CB.Message r)
deriving instance Show r => Show (CB.Event r)
