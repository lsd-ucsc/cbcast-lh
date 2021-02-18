-- | Indirection module
module Causal.CBCAST.Message
( module X
, module Causal.CBCAST.Message
) where

import Causal.CBCAST.Verification as X

{-@ reflect deliverable @-}
{-@
deliverable :: p:Proc -> {m:Message r | compatibleVCsMP m p} -> Bool @-}
deliverable :: Proc -> Message r -> Bool
deliverable p m = deliverable2 m p
