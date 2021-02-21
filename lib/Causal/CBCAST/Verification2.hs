{-# LANGUAGE GADTs #-}
-- | Live translation of the things Gan does in agda
--
-- Status: Incomplete, abandoned
module Causal.CBCAST.Verification2 where

{-@ type Clock = {c:Integer | 0 <= c} @-}
type Clock = Integer

{-@ type Pid = Nat @-}
type Pid = Int

{-@ type Vc = [{c:Clock | 0 <= c}] @-}
type Vc = [Clock]

data Message where
    Message :: {mSenderId::Pid, mSenderVc::Vc} -> Message
{-@
data Message where
    Message :: senderId:Pid -> {senderVc:Vc | senderId < len senderVc}  -> Message
@-}
{-@ measure mSenderId @-}
{-@ measure mSenderVc @-}

{-@ reflect bang @-}
{-@ bang :: v:Vc -> {idx:Pid | idx < len v} -> Clock @-}
bang :: Vc -> Pid -> Clock
bang [] _ = impossibleConst 0 "precondition: idx < len v"
bang (c:cs) p
    | p == 0    = c
    | otherwise = bang cs (p-1)

{-@
type Deliverable
    =  n:Pid
    -> m:Message
    -> receiverVc:Vc
    -> {k:Pid| k < n}
    -> {b:Bool | b <=>
         (    (k == mSenderId m) => (bang (mSenderVc m) k == (bang receiverVc k) + 1)
           && (k /= mSenderId m) => (bang (mSenderVc m) k <= (bang receiverVc k))
         )
       }
@-}

{-@ deliverable :: Deliverable @-}
deliverable :: Pid -> Message -> Vc -> Pid -> Bool
deliverable _ _ _ _ = undefined -- LH finds this implementation lacking

-- | Implementation of 'impossible' lifted to specifications. similar to the
-- one in 'liquid-prelude:Language.Haskell.Liquid.ProofCombinators' but with an
-- argument of the type which must be returned.
{-@ reflect impossibleConst @-}
{-@ impossibleConst :: a -> {v:b | false } -> a @-}
impossibleConst :: a -> b -> a
impossibleConst a _ = a
