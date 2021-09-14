{-# LANGUAGE NamedFieldPuns #-}
module Experiments.CausalDeliverySemanticsDummy where

import Redefined.Set

import Data.BinaryRelation

-- NOTE 
--
-- THIS SEMANTICS IS ALMOST THE SAME AS CausalDeliverySemantics EXCEPT THE
-- ORDER OF THE DELIVERED RELATION IS SWAPPED.
--
-- THE ONLY PURPOSE OF THIS SEMANTICS IS TO TRY OUT THE "SIMULATION" PROOF
-- TECHNIQUE.

-- * Causal Delivery semantics

newtype Process = Process Integer deriving (Eq, Ord)
newtype Message = Message Integer deriving (Eq, Ord)

data State = State
    { delivered :: BinaryRelation Message Process -- The process delivered the message.
    , requires :: BinaryRelation Message Message -- The first message requires the second message.
    }

data Rule
    = Send{sender::Process, message::Message}
    | Deliver{p0::Process, receiver::Process, message::Message}

{-@ reflect messageIsFresh @-}
messageIsFresh :: State -> Message -> Bool
messageIsFresh State{delivered,requires} msg
    =  not (msg `setMember` brDomain delivered)
    && not (msg `setMember` brDomain requires)
    && not (msg `setMember` brRange requires)

{-@ reflect premisesHold @-}
premisesHold :: State -> Rule -> Bool
premisesHold state Send{message}
    =  messageIsFresh state message
premisesHold State{delivered,requires} Deliver{p0,receiver,message}
    =  p0 /= receiver -- A message is delivered to its own sender in the send rule.
    && (message, p0) `setMember` delivered -- The message is a real message sent by some process using the send rule (not necessarily p0).
    && not ((message, receiver) `setMember` delivered) -- The message has not yet been delivered by the receiver (exactly once delivery).
    && brRangeFor requires message  `setIsSubsetOf` brDomainFor delivered receiver

{-@ reflect causalDeliverySemantics @-}
{-@ causalDeliverySemantics :: s:State -> {r:Rule | premisesHold s r} -> State @-}
causalDeliverySemantics :: State -> Rule -> State
causalDeliverySemantics State{delivered,requires} Send{sender,message}
    = State
        { delivered = delivered `setUnion` setSingleton (message, sender)
        , requires = requires `setUnion` brWithRange message (brDomainFor delivered sender)
        }
causalDeliverySemantics state@State{delivered,requires=_} Deliver{receiver,message}
    = state
        { delivered = delivered `setUnion` setSingleton (message, receiver)
        }
