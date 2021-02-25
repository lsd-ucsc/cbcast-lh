-- | Implementation of vector clocks and safety proof for deliverability
-- predicate. Safety proof uses implementation components as part of the spec.
module Causal.CBCAST.Verification where

import Language.Haskell.Liquid.ProofCombinators
import Redefined

-- $setup
-- >>> instance Show (a -> b) where show _ = "fun"


-- * Vector clocks

-- | Clock values are an unbound-integer natural.
{-@
type Clock = {c:Integer | 0 <= c} @-}
type Clock = Integer

-- | LH specs are parameterized over @procCount@, but no value is given.
{-@ measure procCount :: Nat @-}
{-@ type ProcCount = {s:Nat | s == procCount} @-}

-- | A vector clock is a list of clock values of some known length.
{-@
data VC = VC (Vec Clock {procCount}) @-}
data VC = VC [Clock] deriving (Eq, Show)

-- | PID is an index into a vector clock.
{-@
type PID = Fin {procCount} @-}
type PID = Fin

-- | Read an index in a vector clock.
--
-- >>> VC [9,8,7] `vcReadK` 0
-- 9
-- >>> VC [9,8,7] `vcReadK` 1
-- 8
-- >>> VC [9,8,7] `vcReadK` 2
-- 7
-- 
{-@ reflect vcReadK @-}
{-@
vcReadK :: VC -> PID -> Clock @-}
vcReadK :: VC -> PID -> Clock
vcReadK (VC xs) k = listIndex xs k

-- | Infix alias for 'vcReadK' with high precedence.
{-@ reflect ! @-}
{-@
(!) :: VC -> PID -> Clock @-}
(!) :: VC -> PID -> Clock
vc ! p = vcReadK vc p
infixl 9 !

-- | Compare less-equal at a single index the vector clocks.
{-@ reflect vcLessEqualK @-}
{-@
vcLessEqualK :: VC -> VC -> PID -> Bool @-}
vcLessEqualK :: VC -> VC -> PID -> Bool
vcLessEqualK a b k = a ! k <= b ! k

-- | Compare less-equal at a single index the vector clocks. Vector clock less
-- allows for equality at some indexes, but not all indexes, so this
-- implementation must check that the clocks aren't equal.
{-@ reflect vcLessK @-}
{-@
vcLessK :: VC -> VC -> PID -> Bool @-}
vcLessK :: VC -> VC -> PID -> Bool
vcLessK a b k = vcLessEqualK a b k && a /= b

-- NOTE: We take `foldl` as part of our TCB and redefine these operations over
-- all K after the safety proof.


-- * Messages and operations

{-@
data Msg = Msg { senderId :: PID, messageVc :: VC } @-}
data Msg = Msg { senderId :: PID, messageVc :: VC }

-- | page 7/278:
--
--      "The execution of a process is a partial ordered sequence of _events_,
--      each corresponding to the execution of an indivisible action. An
--      acyclic event order, denoted ->^p, reflects the dependence of events
--      occuring at process p upon one another."
--
--      "As Lamport [17], we define the potential causality relation for the
--      system, ->, as the transitive closure of the relation defined as
--      follows:
--
--      (1) if there-exists p: e ->^p e' then e -> e'
--      (2) for-all m: send(m) -> rcv(m)"
--
--      "For messages m and m', the notation m -> m' will be used as a
--      shorthand for send(m) -> send(m')."
--
-- Therefore 'causallyBeforeK' is an alias for 'vcLessK' with respect to
-- message sent times.
--
{-@ reflect causallyBeforeK @-}
{-@
causallyBeforeK :: Msg -> Msg -> PID -> Bool @-}
causallyBeforeK :: Msg -> Msg -> PID -> Bool
causallyBeforeK m1 m2 k = vcLessK (messageVc m1) (messageVc m2) k

-- | Property: 'causallyBeforeK' is true at all indexes.
{-@
type CausallyBeforeProp M1 M2 = k:PID -> { _:Proof | causallyBeforeK M1 M2 k } @-}
type CausallyBeforeProp = PID -> Proof

-- | page 11/282:
--
--      "Observe first that m_1 -> m_2, hence VT(m_1) < VT(m_2) (basic property
--      of vector times)."
--
{-@ ple vectorClocksConsistentWithCausalityProof @-}
{-@
vectorClocksConsistentWithCausalityProof :: m1:Msg -> m2:Msg -> CausallyBeforeProp {m1} {m2} -> k:PID -> { _:Proof | vcLessK (messageVc m1) (messageVc m2) k } @-}
vectorClocksConsistentWithCausalityProof :: Msg -> Msg -> CausallyBeforeProp -> PID -> Proof
vectorClocksConsistentWithCausalityProof _ _ m1_before_m2 k = m1_before_m2 k

{-@ ple causallyBeforeKvcLessKAliasProof @-}
{-@
causallyBeforeKvcLessKAliasProof :: m1:Msg -> m2:Msg -> k:PID -> { _:Proof | causallyBeforeK m1 m2 k <=> vcLessK (messageVc m1) (messageVc m2) k } @-}
causallyBeforeKvcLessKAliasProof :: Msg -> Msg -> PID -> Proof
causallyBeforeKvcLessKAliasProof _m1 _m2 _k = trivial


-- * Processes and operations

{-@
data Proc = Proc { procId :: PID, procVc :: VC } @-}
data Proc = Proc { procId :: PID, procVc :: VC }

-- | page 10/281:
--
--      "(2) On reception of message m sent by p_i and timestamped with VT(m),
--      process p_j =/= p_i delays delivery of m until:
--
--          for-all k: 1...n { VT(m)[k] == VT(p_j)[k] + 1 if k == i
--                           { VT(m)[k] <= VT(p_j)[k]     otherwise"
--
{-@ reflect deliverableK @-}
{-@
deliverableK :: Msg -> Proc -> PID -> Bool @-}
deliverableK :: Msg -> Proc -> PID -> Bool
deliverableK msg proc k
    | k == senderId msg = messageVc msg ! k == procVc proc ! k + 1
    | k /= senderId msg = messageVc msg ! k <= procVc proc ! k
    | otherwise = impossibleConst False "all cases covered"

-- | Property: 'deliverableK' is true at all indexes.
{-@
type DeliverableProp M P = k:PID -> { _:Proof | deliverableK M P k } @-}
type DeliverableProp = PID -> Proof


-- * Safety proof

-- | @processOrderAxiom@ says that every message sent by a given process has a
-- unique VC value at the sender position. (This follows from the fact that
-- events on a process have a total order.) This is enough to prove safety in
-- the same-sender case, because we already know that m1 -> m2, so we know that
-- for each position i in their respective VCs, VC(m1)[i] <= VC(m2)[i]. This
-- axiom rules out the case where they're equal, so then we know that VC(m1)[i]
-- < VC(m2)[i], which is the fact that LH needs to complete the proof.
{-@
assume processOrderAxiom
    ::  m1 : Msg
    ->  m2 : Msg
    ->  { _:Proof | senderId m1 == senderId m2 }
    ->  { _:Proof | vcReadK (messageVc m1) (senderId m1) != vcReadK (messageVc m2) (senderId m2) }
@-}
processOrderAxiom :: Msg -> Msg -> Proof -> Proof
processOrderAxiom _m1 _m2 _proof = ()

-- | page 8/279:
--
--      "Two types of delivery ordering will be of interest here. We define the
--      causal delivery ordering for multicast messages m and m' as follows:
--
--          m -> m' => for-all p element-of dests(m) intersect dests(m'):
--                      deliver(m) ->^p deliver(m')
--
--      CBCAST provides only the causal delivery ordering."
--
-- page 10/281:
--
--      "Suppose that a set of processes P communicate using only broadcasts to
--      the full set of processes in the system; that is,
--      for-all m: dests(m) = P."
--
--      "We now develop a _delivery protocol_ by which each process p receives
--      messages sent to it, delays them if necessary, and then delivers them
--      in an order consistent with causality:
--
--          m -> m' => for-all p: deliver_p(m) ->^p deliver_p(m')"
--
{-@ ple safetyProof @-}
{-@
safetyProof
    ::  p : Proc
    ->  m1 : Msg
    ->  m2 : Msg
    ->  DeliverableProp m1 p
    ->  CausallyBeforeProp m1 m2
    ->  DeliverableProp m2 p
    ->  { _:Proof | false}
@-}
safetyProof :: Proc -> Msg -> Msg -> DeliverableProp -> CausallyBeforeProp -> DeliverableProp -> Proof
safetyProof _p m1 m2 m1_d_p m1_before_m2 m2_d_p
    | senderId m1 == senderId m2
        =   ()
            ? m1_d_p (senderId m1)
            ? m2_d_p (senderId m2)
            ? processOrderAxiom m1 m2 ()
            *** QED
    | otherwise
        =   ()
            ? m1_before_m2 (senderId m1)
            ? m1_d_p (senderId m1)
            ? m2_d_p (senderId m1)
            *** QED


-- * Implementations over all K

-- | And the results of calling the function at each possible vector clock
-- index.
{-@ reflect andAtEachK @-}
{-@
andAtEachK :: (PID -> Bool) -> {v:Nat | v <= procCount} -> Bool @-}
andAtEachK :: (PID -> Bool) -> Int -> Bool
andAtEachK f n = listFoldl boolAnd True (listMap f (fin n))

-- | Compare two vector clocks with elementwise less-equal.
--
-- >>> vcLessEqual (VC []) (VC [])
-- True
-- >>> vcLessEqual (VC [0,0]) (VC [0,0])
-- True
--
-- >>> vcLessEqual (VC [0,1]) (VC [0,2])
-- True
-- >>> vcLessEqual (VC [2,1]) (VC [1,2])
-- False
--
{-@ reflect vcLessEqual @-}
{-@
vcLessEqual :: VC -> VC -> Bool @-}
vcLessEqual :: VC -> VC -> Bool
vcLessEqual a b = vcLessEqualK a b `andAtEachK` vcSize a

-- | Compare two vector clocks. Are they ordered and distinct?
--
-- >>> vcLess (VC []) (VC [])
-- False
-- >>> vcLess (VC [0,0]) (VC [0,0])
-- False
--
-- >>> vcLess (VC [0,1]) (VC [0,2])
-- True
-- >>> vcLess (VC [2,1]) (VC [1,2])
-- False
--
{-@ reflect vcLess @-}
{-@
vcLess :: VC -> VC -> Bool @-}
vcLess :: VC -> VC -> Bool
vcLess (VC []) (VC []) = False
vcLess a b = vcLessK a b `andAtEachK` vcSize a

-- | As with 'vcLessK' and 'causallyBeforeK', this 'causallyBefore' is
-- effectively an alias for 'vcLess' with respect to message sent times.
--
{-@ reflect causallyBefore @-}
{-@
causallyBefore :: Msg -> Msg -> Bool @-}
causallyBefore :: Msg -> Msg -> Bool
causallyBefore m1 m2 = causallyBeforeK m1 m2 `andAtEachK` vcSize (messageVc m1)

-- | @deliverableImpl m p@ computes whether a message sent by @senderId m@ at @messageVc
-- m@ is deliverable to @procId p@ at @procVc p@.
--
--
-- Example:
--
-- P0 and P1 both start at [0,0].
-- >    P0@[0,0]    P1@[0,0]
--
-- P0 sends "hello" causing it to increment its own vector clock and append
-- that to the message.
-- >    P0@[1,0]    P1@[0,0]
--
-- P1 receives the message from P0, delivers it, and applies the attached
-- vector clock.
-- >    P0@[1,0]    P1@[1,0]
--
-- P1 sends "world" causing it to increment its own vector clock and append
-- that to the message.
-- >    P0@[1,0]    P1@[1,1]
--
-- What does P0 think of the deliverability of both messages?
--
-- * The "hello"@[1,0] is not deliverable at P0.
-- * The "world"@[1,1] is deliverable at P0.
--
-- From this we conclude that "Process p_j need not delay messages received
-- from itself" means that it actually _cannot_ delay such messages, since they
-- won't be considered deliverable. This interpretation is bolstered by the
-- precondition in (2) "On reception of message m sent by p_i, process p_j =/=
-- p_i delays delivery".
--
-- >>> let p = Proc 0 $ VC [1,0]
-- >>> deliverableImpl (Msg 0 $ VC [1,0]) p -- "hello" message
-- False
-- >>> deliverableImpl (Msg 1 $ VC [1,1]) p -- "world" message
-- True
--
{-@ reflect deliverableImpl @-}
{-@
deliverableImpl :: Msg -> Proc -> Bool @-}
deliverableImpl :: Msg -> Proc -> Bool
deliverableImpl msg proc = deliverableK msg proc `andAtEachK` vcSize (messageVc msg)


-- * Additional vector clock functions

-- | Compare two vector clocks. Are they concurrent?
--
-- >>> vcIndependent (VC []) (VC [])
-- True
-- >>> vcIndependent (VC [0,0]) (VC [0,0])
-- True
--
-- >>> vcIndependent (VC [0,1]) (VC [0,2])
-- False
-- >>> vcIndependent (VC [2,1]) (VC [1,2])
-- True
--
{-@ reflect vcIndependent @-}
{-@
vcIndependent :: VC -> VC -> Bool @-}
vcIndependent :: VC -> VC -> Bool
vcIndependent a b = not (vcLess a b) && not (vcLess b a)

{-@ measure vcSize @-}
{-@
vcSize :: VC -> {s:Nat | s == procCount} @-}
vcSize :: VC -> Int
vcSize (VC []) = 0
vcSize (VC xs@(_:_)) = listLength xs

{-@ reflect vcNew @-}
{-@
vcNew :: ProcCount -> VC @-}
vcNew :: Int -> VC
vcNew size = VC (listReplicate size 0)

-- | Increment the index in a vector clock.
--
-- >>> vcTick 0 (VC [9,8,7])
-- VC [10,8,7]
-- >>> vcTick 1 (VC [9,8,7])
-- VC [9,9,7]
-- >>> vcTick 2 (VC [9,8,7])
-- VC [9,8,8]
--
-- >>> vcTick (-1) (VC [9,8,7])
-- VC [9,8,7]
-- >>> vcTick 3 (VC [9,8,7])
-- VC [9,8,7]
--
{-@ reflect vcTick @-}
{-@
vcTick :: PID -> VC -> VC @-}
vcTick :: PID -> VC -> VC
vcTick p (VC xs) = VC $ vcTickImpl p xs
{-@ reflect vcTickImpl @-}
{-@
vcTickImpl :: i:Nat -> {xs:[Clock] | i < len xs} -> {ys:[Clock] | len xs == len ys} @-}
vcTickImpl :: Int -> [Clock] -> [Clock]
vcTickImpl _ [] = impossibleConst [] "index is less than list length"
vcTickImpl p (c:cs)
    | p == 0    = (c+1):cs
    | otherwise = c:vcTickImpl (p-1) cs

-- | Combine two vector clocks with elementwise max.
--
-- >>> vcCombine (VC []) (VC [])
-- VC []
-- >>> vcCombine (VC [0,0]) (VC [0,0])
-- VC [0,0]
--
-- >>> vcCombine (VC [0,1]) (VC [0,2])
-- VC [0,2]
-- >>> vcCombine (VC [2,1]) (VC [1,2])
-- VC [2,2]
--
{-@ reflect vcCombine @-}
{-@
vcCombine :: VC -> VC -> VC @-}
vcCombine :: VC -> VC -> VC
vcCombine (VC xs) (VC ys) = VC $ vcCombineImpl xs ys
{-@ reflect vcCombineImpl @-}
{-@
vcCombineImpl :: xs:[Clock] -> {ys:[Clock] | len xs == len ys} -> {zs:[Clock] | len xs == len zs && len ys == len zs} @-}
vcCombineImpl :: [Clock] -> [Clock] -> [Clock]
vcCombineImpl (x:xs) (y:ys) = (if x < y then y else x) : vcCombineImpl xs ys
vcCombineImpl [] [] = []
vcCombineImpl _ _ = impossibleConst [] "lists have same length"
