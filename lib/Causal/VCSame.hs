-- | Implementation of vector clocks as association lists constrained by Liquid
-- Haskell to operate only on those which have the same PIDs.
module Causal.VCSame where
import Redefined
--import Language.Haskell.Liquid.ProofCombinators
import qualified Data.Set as S -- Lifted: Set, empty, singleton, member, union, intersection, difference
import Data.UUID (UUID)


type Assoc k v = [(k, v)]


{-@ measure keySet @-}
keySet :: Ord k => Assoc k v -> S.Set k
keySet [] = S.empty
keySet ((k,_):rest) = S.singleton k `S.union` keySet rest

{-@ inline hasKey @-}
hasKey :: Ord k => k -> Assoc k v -> Bool
hasKey k xs = k `S.member` keySet xs

-- {-@ measure keyList @-}
-- keyList :: Assoc k v -> [k]
-- keyList ((k,_):rest) = k : keyList rest
-- keyList [] = []
--
-- {-@ inline keysMatch @-}
-- keysMatch :: Eq k => Assoc k v -> Assoc k v -> Bool
-- keysMatch a b = keyList a == keyList b
--
-- TODO: find out why the above doesn't work

{-@ reflect keysMatch @-}
keysMatch :: Eq k => Assoc k v -> Assoc k v' -> Bool
keysMatch ((a,_):as) ((b,_):bs) = a == b && keysMatch as bs
keysMatch [] [] = True
keysMatch _ _ = False

-- | Like 'zipWith' but for association lists.
{-@ reflect aZip @-}
{-@ ple aZip @-}
{-@ aZip :: (a -> b -> c) -> xs:Assoc k a -> {ys:Assoc k b | keysMatch xs ys} -> {zs:Assoc k c | keysMatch xs zs && keysMatch ys zs} @-}
aZip :: Eq k => (a -> b -> c) -> Assoc k a -> Assoc k b -> Assoc k c
aZip f ((ak,av):as) ((bk,bv):bs) | ak == bk = (ak, f av bv) : aZip f as bs
aZip _ [] [] = []
aZip _ _ _ = impossibleConst [] "assoc-lists have same keys"
-- TODO: use this to implement vcCombine and vcLessEqual

aNew :: [k] -> v -> Assoc k v
aNew (k:rest) def = (k,def):aNew rest def
aNew [] _ = []
-- TODO: use this to implement vcNew

{-@ ignore aUpdate @-} -- FIXME: this signature deosn't check
{-@ aUpdate :: k -> (v -> v) -> xs:Assoc k v -> {ys:Assoc k v | keysMatch xs ys} @-}
aUpdate :: Eq k => k -> (v -> v) -> Assoc k v -> Assoc k v
aUpdate _ _ [] = []
aUpdate k f ((cur,val):rest)
    | k == cur  = (cur,f val):rest
    | otherwise = (cur,val):aUpdate k f rest
-- TODO: use this to implement vcTick
