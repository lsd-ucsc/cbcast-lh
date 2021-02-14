module Causal.CBCAST.Verification where

import Language.Haskell.Liquid.ProofCombinators

-- $setup
-- >>> :set -XStandaloneDeriving -XDeriveGeneric
-- >>> deriving instance Show Process
-- >>> deriving instance Show r => Show (Message r)
-- >>> import GHC.Generics (Generic)
-- >>> deriving instance Generic Process
-- >>> deriving instance Generic r => Generic (Message r)
-- >>> import qualified Test.QuickCheck as QC
-- >>> :{
-- instance QC.Arbitrary Process where
--     arbitrary = QC.sized $ \n -> do
--         time <- QC.suchThat QC.arbitrary (\xs -> length xs == n)
--         node <- QC.choose (0, length time)
--         return $ Process node time
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
-- >>> -- QC.sample (QC.arbitrary :: QC.Gen Process)


-- * Helpers

-- | Reify the @len@ measure defined in the 'liquid-base:GHC.Base'
-- specification into code and back into specifications.
--
-- prop> length xs == listLength xs
{-@ measure listLength @-}
{-@ listLength :: xs:_ -> {n:Nat | len xs == n } @-}
listLength :: [a] -> Int
listLength [] = 0
listLength (_:xs) = 1 + listLength xs

-- | Implementation of 'impossible' lifted to specifications. similar to the
-- one in 'liquid-prelude:Language.Haskell.Liquid.ProofCombinators' but with an
-- argument of the type which must be returned.
{-@ inline impossibleConst @-}
{-@ impossibleConst :: a -> {v:b | false } -> a @-}
impossibleConst :: a -> b -> a
impossibleConst a _ = a

-- | Implementation of 'and' lifted to specifications. Probably same as
-- 'Prelude'.
--
-- prop> and xs == listAnd xs
{-@ reflect listAnd @-} -- FIXME: this causes a crash when it's a measure?
listAnd :: [Bool] -> Bool
listAnd [] = True
listAnd (b:bs) = b && listAnd bs


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

-- | Read the index in a vector clock. Probably similar to (!!) but doesn't
-- crash when out of bounds.
--
-- >>> [9,8,7] ! 0
-- 9
-- >>> [9,8,7] ! 1
-- 8
-- >>> [9,8,7] ! 2
-- 7
--
-- >>> [9,8,7] ! (-1)
-- 0
-- >>> [9,8,7] ! 3
-- 0
{-@ reflect ! @-}
{-@
(!) :: xs:VC -> {p:PID | p < len xs} -> Clock @-}
(!) :: VC -> PID -> Clock
[] ! _ = impossibleConst 0 "index is less than list length"
(c:cs) ! p
    | p == 0    = c
    | otherwise = cs ! (p-1)
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
data Process = Process
    { pNode :: PID
    , pTime :: {time:VC | pNode < len time}
    }
@-}
data Process = Process
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
--
-- We interpret this to mean that for `p_j == p_i` a message is deliverable
-- when `VT(m) == VT(p_j)` because (1) means that the process and the message
-- have the same vector clock when it is sent, and "p_j need not delay messages
-- received from itself."
--
-- For `p_j /= p_i` we check the elementwise VC inequality above.
--
-- @deliverable1 m p@ computes whether a message sent by @mSender m@ at @mSent
-- m@ is deliverable to @pNode p@ at @pTime p@. This implementation uses a list
-- comprehension and can't be lifted to specifications.
{-@ deliverable1 :: m:Message r -> {p:Process | len (mSent m) == len (pTime p)} -> Bool @-}
deliverable1 :: Message r -> Process -> Bool
deliverable1 Message{mSender=p_i, mSent=m'VT} Process{pNode=p_j, pTime=p_j'VT}
    | p_j == p_i    = m'VT == p_j'VT
    | otherwise     = listAnd
        [ if k == p_i   then (m'VT ! k) == (p_j'VT ! k) + 1
                        else (m'VT ! k) <= (p_j'VT ! k)
        | k <- [0 .. listLength p_j'VT]
        , 0 <= k && k < listLength p_j'VT
        ]

-- | @deliverable2 m p@ computes whether a message sent by @mSender m@ at
-- @mSent m@ is deliverable to @pNode p@ at @pTime p@. This implementation is
-- almost the same as @deliverable1@ but this one uses explicit recursion
-- instead of a list comprehension.
--
-- prop> length (mSent m) == length (pTime p) ==> deliverable1 m p == deliverable2 m p
{-@ inline deliverable2 @-}
{-@ deliverable2 :: m:Message r -> {p:Process | len (mSent m) == len (pTime p)} -> Bool @-}
deliverable2 :: Message r -> Process -> Bool
deliverable2 Message{mSender=p_i, mSent=m'VT} Process{pNode=p_j, pTime=p_j'VT}
    | p_j == p_i    = m'VT == p_j'VT
    | otherwise     = listAnd (deliverable2Iter k n p_i m'VT p_j'VT)
  where
    k = 0
    n = listLength p_j'VT
{-@ deliverable2Iter :: k:Nat -> n:Nat -> {p_i:PID | p_i < n} -> {m'VT:VC | n == len m'VT} -> {p_j'VT:VC | n == len p_j'VT} -> [Bool] / [n - k] @-}
{-@ reflect deliverable2Iter @-}
deliverable2Iter :: Int -> Int -> PID -> VC -> VC -> [Bool]
deliverable2Iter k n p_i m'VT p_j'VT
    | k < n     = deliverable2Pred k p_i m'VT p_j'VT:deliverable2Iter (k+1) n p_i m'VT p_j'VT
    | otherwise = []
{-@ deliverable2Pred :: k:PID -> p_i:PID -> {m'VT:VC | k < len m'VT && p_i < len m'VT} -> {p_j'VT:VC | k < len p_j'VT && p_i < len p_j'VT} -> Bool @-}
{-@ inline deliverable2Pred @-}
deliverable2Pred :: PID -> PID -> VC -> VC -> Bool
deliverable2Pred k p_i m'VT p_j'VT
    | k == p_i  = (m'VT ! k) == (p_j'VT ! k) + 1
    | otherwise = (m'VT ! k) <= (p_j'VT ! k)

-- | @deliverable3 m p@ computes whether a message sent by @mSender m@ at
-- @mSent m@ is deliverable to @pNode p@ at @pTime p@. This implementation is
-- more efficient than @deliverable1@ and @deliverable2@.
--
-- prop> length (mSent m) == length (pTime p) ==> deliverable1 m p == deliverable3 m p
-- prop> length (mSent m) == length (pTime p) ==> deliverable2 m p == deliverable3 m p
{-@ inline deliverable3 @-}
{-@ deliverable3 :: m:Message r -> {p:Process | len (mSent m) == len (pTime p)} -> Bool @-}
deliverable3 :: Message r -> Process -> Bool
deliverable3 Message{mSender=p_i, mSent=m'VT} Process{pNode=p_j, pTime=p_j'VT}
    | p_j == p_i    = m'VT == p_j'VT
    | otherwise     = deliverable3Iter p_i m'VT p_j'VT
{-@ reflect deliverable3Iter @-}
{-@ deliverable3Iter :: Int -> m'VT:VC -> {p_j'VT:VC | len m'VT == len p_j'VT} -> Bool @-}
deliverable3Iter :: PID -> VC -> VC -> Bool
deliverable3Iter p_i (mClock:mRest) (pClock:pRest)
    | p_i == 0  = mClock == pClock + 1  && deliverable3Iter (p_i-1) mRest pRest
    | otherwise = mClock <= pClock      && deliverable3Iter (p_i-1) mRest pRest
deliverable3Iter _ [] [] = True
deliverable3Iter _ _ _ = impossibleConst False "VCs have same length"

{-@ ple proofDeliverable2SameAs3 @-}
{-@
proofDeliverable2SameAs3
    :: m:Message r
    -> p:Process
    -> {deliverable2 m p <=> deliverable3 m p}
@-}
proofDeliverable2SameAs3 :: Message r -> Process -> Proof
proofDeliverable2SameAs3 Message{} Process{}
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
{-@ causallyBefore :: a:Message r -> {b:Message r | len (mSent a) == len (mSent b)} -> Bool @-}
causallyBefore :: Message r -> Message r -> Bool
causallyBefore a b = mSent a `vcLess` mSent b

-- page 11/282:
--
--      "Observe first that m_1 -> m_2, hence VT(m_1) < VT(m_2) (basic property
--      of vector times)."

{-@ proofVectorClocksConsistentWithCausality :: m1:Message r -> {m2:Message r | causallyBefore m1 m2} -> { vcLess (mSent m1) (mSent m2) } @-}
proofVectorClocksConsistentWithCausality :: Message r -> Message r -> Proof
proofVectorClocksConsistentWithCausality _ _ = () *** QED

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
    :: p:Process
    -> {m1:Message r | deliverable2 m1 p}
    -> {m2:Message r | causallyBefore m1 m2}
    -> {not (deliverable2 m2 p)}
@-}
proofSafety :: Process -> Message r -> Message r -> Proof
proofSafety Process{} Message{} Message{}
    =   ()
    *** Admit -- TODO
