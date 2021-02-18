module Causal.CBCAST.Verification where

import Language.Haskell.Liquid.ProofCombinators

import Redefined

-- $setup
-- >>> :set -XStandaloneDeriving -XDeriveGeneric
-- >>> deriving instance Show Proc
-- >>> deriving instance Show r => Show (Message r)
-- >>> import GHC.Generics (Generic)
-- >>> deriving instance Generic Proc
-- >>> deriving instance Generic r => Generic (Message r)
-- >>> import qualified Test.QuickCheck as QC
-- >>> :{
-- instance QC.Arbitrary Proc where
--     arbitrary = QC.sized $ \n -> do
--         time <- QC.suchThat QC.arbitrary (\xs -> length xs == n)
--         node <- QC.choose (0, length time)
--         return $ Proc node time
--     shrink = QC.recursivelyShrink
-- :}
--
-- >>> :{
-- instance QC.Arbitrary r => QC.Arbitrary (Message r) where
--     arbitrary = QC.sized $ \n -> do
--         sent <- QC.suchThat QC.arbitrary (\xs -> length xs == n)
--         sender <- QC.choose (0, length sent)
--         raw <- QC.arbitrary
--         return $ Message sender sent raw
--     shrink m =
--         [ Message sender sent raw
--         | (sender, sent, raw) <- QC.shrink (mSender m, mSent m, mRaw m)
--         ]
-- :}
--
-- >>> -- QC.sample (QC.arbitrary :: QC.Gen (Message String))
-- >>> -- QC.sample (QC.arbitrary :: QC.Gen Proc)


-- * Vector clocks

{-@
type Clock = {c:Integer | clockMin <= c} @-}
type Clock = Integer

{-@ inline clockMin @-}
{-@
clockMin :: Clock @-}
clockMin :: Clock
clockMin = 0

{-@
type VC = [Clock] @-}
type VC = [Clock]

{-@
type PID = Nat @-}
type PID = Int

{-@ inline vcNew @-}
{-@
vcNew :: n:Nat -> {vc:VC | n == len vc} @-}
vcNew :: Int -> VC
vcNew size = listReplicate size clockMin

-- | Read the index in a vector clock. Similar to (!!) but doesn't crash when
-- out of bounds.
--
-- >>> vcRead [9,8,7] 0
-- 9
-- >>> vcRead [9,8,7] 1
-- 8
-- >>> vcRead [9,8,7] 2
-- 7
--
-- >>> vcRead [9,8,7] (-1)
-- 0
-- >>> vcRead [9,8,7] 3
-- 0
{-@ reflect vcRead @-}
{-@
vcRead :: xs:VC -> {p:PID | p < len xs} -> Clock @-}
vcRead :: VC -> PID -> Clock
vcRead [] _ = impossibleConst 0 "index is less than list length"
vcRead (c:cs) p
    | p == 0    = c
    | otherwise = vcRead cs (p-1)

-- | Alias for 'vcRead'
{-@ inline ! @-}
{-@
(!) :: xs:VC -> {p:PID | p < len xs} -> Clock @-}
(!) :: VC -> PID -> Clock
cs ! p = vcRead cs p
infixl 9 !

-- | Increment the index in a vector clock.
--
-- >>> vcTick 0 [9,8,7]
-- [10,8,7]
-- >>> vcTick 1 [9,8,7]
-- [9,9,7]
-- >>> vcTick 2 [9,8,7]
-- [9,8,8]
--
-- >>> vcTick (-1) [9,8,7]
-- [9,8,7]
-- >>> vcTick 3 [9,8,7]
-- [9,8,7]
--
{-@ reflect vcTick @-}
{-@
vcTick :: p:PID -> {xs:VC | p < len xs} -> {ys:VC | len xs == len ys} @-}
vcTick :: PID -> VC -> VC
vcTick _ [] = impossibleConst [] "index is less than list length"
vcTick p (c:cs)
    | p == 0    = (c+1):cs
    | otherwise = c:vcTick (p-1) cs

-- | Combine two vector clocks with elementwise max.
--
-- >>> vcCombine [] []
-- []
-- >>> vcCombine [0,0] [0,0]
-- [0,0]
--
-- >>> vcCombine [0,1] [0,2]
-- [0,2]
-- >>> vcCombine [2,1] [1,2]
-- [2,2]
--
{-@ reflect vcCombine @-}
{-@
vcCombine :: xs:VC -> {ys:VC | len xs == len ys} -> {zs:VC | len xs == len zs && len ys == len zs} @-}
vcCombine :: VC -> VC -> VC
vcCombine (x:xs) (y:ys) = (if x < y then y else x) : vcCombine xs ys
vcCombine [] [] = []
vcCombine _ _ = impossibleConst [] "lists have same length"

-- | Compare two vector clocks with elementwise less-equal.
--
-- >>> vcLessEqual [] []
-- True
-- >>> vcLessEqual [0,0] [0,0]
-- True
--
-- >>> vcLessEqual [0,1] [0,2]
-- True
-- >>> vcLessEqual [2,1] [1,2]
-- False
--
{-@ reflect vcLessEqual @-}
{-@
vcLessEqual :: xs:VC -> {ys:VC | len xs == len ys} -> Bool @-}
vcLessEqual :: VC -> VC -> Bool
vcLessEqual (x:xs) (y:ys) = x <= y && vcLessEqual xs ys
vcLessEqual [] [] = True
vcLessEqual _ _ = impossibleConst False "lists have same length"

-- | Compare two vector clocks. Are they ordered and distinct?
--
-- >>> vcLess [] []
-- False
-- >>> vcLess [0,0] [0,0]
-- False
--
-- >>> vcLess [0,1] [0,2]
-- True
-- >>> vcLess [2,1] [1,2]
-- False
--
{-@ inline vcLess @-}
{-@
vcLess :: xs:VC -> {ys:VC | len xs == len ys} -> Bool @-}
vcLess :: VC -> VC -> Bool
vcLess a b = vcLessEqual a b && a /= b

-- | Compare two vector clocks. Are they concurrent?
--
-- >>> vcIndependent [] []
-- True
-- >>> vcIndependent [0,0] [0,0]
-- True
--
-- >>> vcIndependent [0,1] [0,2]
-- False
-- >>> vcIndependent [2,1] [1,2]
-- True
--
{-@ inline vcIndependent @-}
{-@
vcIndependent :: xs:VC -> {ys:VC | len xs == len ys} -> Bool @-}
vcIndependent :: VC -> VC -> Bool
vcIndependent a b = not (vcLess a b) && not (vcLess b a)


-- * Deliverability

{-@
data Proc = Proc
    { pNode :: PID
    , pTime :: {time:VC | pNode < len time}
    }
@-}
data Proc = Proc
    { pNode :: PID
    , pTime :: VC
    }

{-@
data Message raw = Message
    { mSender :: PID
    , mSent :: {sent:VC | mSender < len sent}
    , mRaw :: raw
    }
@-}
data Message raw = Message
    { mSender :: PID
    , mSent :: VC
    , mRaw :: raw
    }

{-@ inline compatibleVCsMP @-}
compatibleVCsMP :: Message r -> Proc -> Bool
compatibleVCsMP m p = listLength (mSent m) == listLength (pTime p)

{-@ reflect compatibleVCsMM @-} -- FIXME: this doesn't work with inline?
compatibleVCsMM :: Message r -> Message r -> Bool
compatibleVCsMM a b = listLength (mSent a) == listLength (mSent b)

-- | Determine message deliverability at a process.
--
--      "(1) Before sending m, process p_i increments VT(p_i)[i] and timestamps
--      m.
--
--      (2) On reception of message m sent by p_i and timestamped with VT(m),
--      process p_j =/= p_i delays delivery of m until:
--
--          for-all k: 1...n { VT(m)[k] == VT(p_j)[k] + 1 if k == i
--                           { VT(m)[k] <= VT(p_j)[k]     otherwise
--
--      Process p_j need not delay messages received from itself."
{-@
type Deliverable r
    =  n:PID
    -> m:Message r
    -> p:Proc
    -> {k:PID| k < n}
    -> {b:Bool | b <=>
         (    (k == mSenderId m) => (vcRead (mSenderVc m) k == vcRead (pTime p) k + 1)
           && (k /= mSenderId m) => (vcRead (mSenderVc m) k <= vcRead (pTime p) k    )
         )
       }
@-}

-- | Example:
--
-- P0 and P1 both start at [0,0].
-- >    P0@[0,0]    P1@[0,0]
-- P0 sends "hello" causing it to increment its own vector clock and append
-- that to the message.
-- >    P0@[1,0]    P1@[0,0]
-- P1 receives the message from P0, delivers it, and applies the attached
-- vector clock.
-- >    P0@[1,0]    P1@[1,0]
-- P1 sends "world" causing it to increment its own vector clock and append
-- that to the message.
-- >    P0@[1,0]    P1@[1,1]
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
-- >>> let p = Proc 0 [1,0]
-- >>> deliverable1 (Message 0 [1,0] "hello") p
-- False
-- >>> deliverable1 (Message 1 [1,1] "world") p
-- True
--
-- @deliverable1 m p@ computes whether a message sent by @mSender m@ at @mSent
-- m@ is deliverable to @pNode p@ at @pTime p@. This implementation uses a list
-- comprehension and can't be lifted to specifications.
{-@ deliverable1 :: m:Message r -> {p:Proc | compatibleVCsMP m p} -> Bool @-}
deliverable1 :: Message r -> Proc -> Bool
deliverable1 m@Message{mSender=mID, mSent=mVT} p@Proc{pTime=pVT}
    | not (compatibleVCsMP m p) = impossibleConst False "VCs have same length" -- FIXME this case reestablishes the precondition in the rest of the body wherever deliverable is used
    | otherwise = listAnd
        [ if k == mID   then (mVT ! k) == (pVT ! k) + 1
                        else (mVT ! k) <= (pVT ! k)
        | k <- [0 .. listLength pVT]
        , 0 <= k && k < listLength pVT
        ]

-- | @deliverable2 m p@ computes whether a message sent by @mSender m@ at
-- @mSent m@ is deliverable to @pNode p@ at @pTime p@. This implementation is
-- almost the same as @deliverable1@ but this one uses explicit recursion
-- instead of a list comprehension.
--
-- prop> length (mSent m) == length (pTime p) ==> deliverable1 m p == deliverable2 m p
{-@ inline deliverable2 @-}
{-@ deliverable2 :: m:Message r -> {p:Proc | compatibleVCsMP m p} -> Bool @-}
deliverable2 :: Message r -> Proc -> Bool
deliverable2 m@Message{mSender=mID, mSent=mVT} p@Proc{pTime=pVT}
    | not (compatibleVCsMP m p) = impossibleConst False "VCs have same length" -- FIXME this case reestablishes the precondition in the rest of the body wherever deliverable is used
    | otherwise = listAnd (deliverable2Iter k n mID mVT pVT)
  where
    k = 0
    n = listLength pVT
{-@ deliverable2Iter :: k:Nat -> n:Nat -> {mID:PID | mID < n} -> {mVT:VC | n == len mVT} -> {pVT:VC | n == len pVT} -> [Bool] / [n - k] @-}
{-@ reflect deliverable2Iter @-}
deliverable2Iter :: Int -> Int -> PID -> VC -> VC -> [Bool]
deliverable2Iter k n mID mVT pVT
    | k < n     = deliverable2Pred k mID mVT pVT:deliverable2Iter (k+1) n mID mVT pVT
    | otherwise = []
{-@ deliverable2Pred :: k:PID -> mID:PID -> {mVT:VC | k < len mVT && mID < len mVT} -> {pVT:VC | k < len pVT && mID < len pVT} -> Bool @-}
{-@ inline deliverable2Pred @-}
deliverable2Pred :: PID -> PID -> VC -> VC -> Bool
deliverable2Pred k mID mVT pVT
    | k == mID  = (mVT ! k) == (pVT ! k) + 1
    | otherwise = (mVT ! k) <= (pVT ! k)

-- | @deliverable3 m p@ computes whether a message sent by @mSender m@ at
-- @mSent m@ is deliverable to @pNode p@ at @pTime p@. This implementation is
-- more efficient than @deliverable1@ and @deliverable2@.
--
-- prop> length (mSent m) == length (pTime p) ==> deliverable1 m p == deliverable3 m p
-- prop> length (mSent m) == length (pTime p) ==> deliverable2 m p == deliverable3 m p
{-@ inline deliverable3 @-}
{-@ deliverable3 :: m:Message r -> {p:Proc | compatibleVCsMP m p} -> Bool @-}
deliverable3 :: Message r -> Proc -> Bool
deliverable3 m@Message{mSender=mID, mSent=mVT} p@Proc{pTime=pVT}
    | not (compatibleVCsMP m p) = impossibleConst False "VCs have same length" -- FIXME this case reestablishes the precondition in the rest of the body wherever deliverable is used
    | otherwise = deliverable3Iter mID mVT pVT
{-@ reflect deliverable3Iter @-}
{-@ deliverable3Iter :: Int -> mVT:VC -> {pVT:VC | len mVT == len pVT} -> Bool @-}
deliverable3Iter :: PID -> VC -> VC -> Bool
deliverable3Iter mID (mClock:mRest) (pClock:pRest)
    | mID == 0  = mClock == pClock + 1  && deliverable3Iter (mID-1) mRest pRest
    | otherwise = mClock <= pClock      && deliverable3Iter (mID-1) mRest pRest
deliverable3Iter _ [] [] = True
deliverable3Iter _ _ _ = impossibleConst False "VCs have same length"

{-@ ple proofDeliverable2SameAs3 @-}
{-@
proofDeliverable2SameAs3
    :: m:Message r
    -> p:Proc
    -> {deliverable2 m p <=> deliverable3 m p}
@-}
proofDeliverable2SameAs3 :: Message r -> Proc -> Proof
proofDeliverable2SameAs3 Message{} Proc{}
    =   ()
    *** Admit -- TODO


-- * Safety

-- page 7/278:
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

{-@ inline causallyBefore @-}
{-@ causallyBefore :: a:Message r -> {b:Message r | compatibleVCsMM a b} -> Bool @-}
causallyBefore :: Message r -> Message r -> Bool
causallyBefore a b
    | not (compatibleVCsMM a b) = impossibleConst False "VCs have same length" -- FIXME this case reestablishes the precondition in the rest of the body wherever deliverable is used
    | otherwise = mSent a `vcLess` mSent b

-- page 11/282:
--
--      "Observe first that m_1 -> m_2, hence VT(m_1) < VT(m_2) (basic property
--      of vector times)."

{-@ proofVectorClocksConsistentWithCausality :: m1:Message r -> {m2:Message r | causallyBefore m1 m2} -> { vcLess (mSent m1) (mSent m2) } @-}
proofVectorClocksConsistentWithCausality :: Message r -> Message r -> Proof
proofVectorClocksConsistentWithCausality _ _ = trivial

-- page 8/279:
--
--      "Two types of delivery ordering will be of interest here. We define the
--      causal delivery ordering for multicast messages m and m' as follows:
--
--          m -> m' => for-all p element-of dests(m) intersect dests(m'):
--                      deliver(m) ->^p deliver(m')
--
--      CBCAST provides only the causal delivery ordering."

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

{-@ ple proofSafety @-}
{-@
proofSafety
    :: p:Proc
    -> {m1:Message r | deliverable2 m1 p}
    -> {m2:Message r | causallyBefore m1 m2}
    -> {not (deliverable2 m2 p)}
@-}
proofSafety :: Proc -> Message r -> Message r -> Proof
proofSafety p@Proc{} m1@Message{} m2@Message{}
    =   (listLength (pTime p) === listLength (mSent m2) *** QED) -- transitivity of compatibility
    &&& (deliverable2 m1 p === causallyBefore m1 m2 *** QED) -- unfold the preconditions
    &&& (deliverable2 m2 p *** Admit) -- uctual proof

-- Notes from Yiyun
--  * Two kinds of automation; SMT constraints & PLE
--      * SMT can handle sentences of boolean logic w/o quantifiers
--          * p | q -> r
--          * Functions bring in forall quantifiers
--      * PLE unfolds reflected functions (which otherwise only have congruence)
--  * Reflected functions need PLE or a proof to establish some postconditions
--      * PLE won't be able to prove things which need induction
--      * `cast` lets you attach a proof into a reflected function (eg. where PLE isn't enough)
--      * eg. vrdt/src/Liquid/Data/Map.hs
