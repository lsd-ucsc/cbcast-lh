{-# LANGUAGE NamedFieldPuns #-}
module Causal.CausalDeliverySemantics where

import Redefined


-- * Tools for semantics

-- ** Tuples

{-@ reflect firstEquals @-}
firstEquals :: Eq a => a -> (a, b) -> Bool
firstEquals a' (a, _b) = a' == a

-- ** Relations

type Relation a b = Set (a, b)

{-@ reflect domain @-}
domain :: Ord a => Relation a b -> Set a
domain = setFromList . listMap tupleFirst . setAscList

{-@ reflect range @-}
range :: Ord b => Relation a b -> Set b
range = setFromList . listMap tupleSecond . setAscList

{-@ reflect rangeFor @-}
-- | Analogue to calling a function, except that a relation can return a set of
-- values for an input.
rangeFor :: (Eq a, Ord b) => a -> Relation a b -> Set b
rangeFor a = setFromList . listMap tupleSecond . listFilter (firstEquals a) . setAscList
--TODO implement with setMap(?) and setFilter

{-@ reflect withRange @-}
-- | Use a value as the domain for an existing range.
withRange :: (Ord a, Ord b) => a -> Set b -> Relation a b
withRange a = setFromList . listMap ((,) a) . setAscList
---TODO withRange :: a -> x:Set b -> {y:Relation a b | setSize x == setSize y} @-}

-- * Causal Delivery semantics

newtype Process = Process Integer deriving (Eq, Ord)
newtype Message = Message Integer deriving (Eq, Ord)

data State = State
    { delivered :: Relation Process Message -- The process delivered the message.
    , requires :: Relation Message Message -- The first message requires the second message.
    }

data Rule
    = Send{sender::Process, message::Message}
    | Deliver{p0::Process, receiver::Process, message::Message}

{-@ reflect messageIsFresh @-}
messageIsFresh :: State -> Message -> Bool
messageIsFresh State{delivered,requires} msg
    =  not (msg `setMember` range delivered)
    && not (msg `setMember` domain requires)
    && not (msg `setMember` range requires)

{-@ reflect premisesHold @-}
premisesHold :: State -> Rule -> Bool
premisesHold state Send{message}
    =  messageIsFresh state message
premisesHold State{delivered,requires} Deliver{p0,receiver,message}
    =  p0 /= receiver -- A message is delivered to its own sender in the send rule.
    && (p0, message) `setMember` delivered -- The message is a real message sent by some process using the send rule (not necessarily p0).
    && not ((receiver, message) `setMember` delivered) -- The message has not yet been delivered by the receiver (exactly once delivery).
    && rangeFor message requires `setIsSubsetOf` rangeFor receiver delivered

{-@ reflect causalDeliverySemantics @-}
{-@ causalDeliverySemantics :: s:State -> {r:Rule | premisesHold s r} -> State @-}
causalDeliverySemantics :: State -> Rule -> State
causalDeliverySemantics State{delivered,requires} Send{sender,message}
    = State
        { delivered = delivered `setUnion` setSingleton (sender, message)
        , requires = requires `setUnion` withRange message (rangeFor sender delivered)
        }
causalDeliverySemantics state@State{delivered,requires} Deliver{receiver,message}
    = state
        { delivered = delivered `setUnion` setSingleton (receiver, message)
        }