module Assoc where

import Language.Haskell.Liquid.ProofCombinators
    (Proof, QED(..), (***), impossible)


-- * Types

type Assoc k v = [(k, v)]
{-@ type Assoc k v = {xs:[(k, v)] | sortedKeys xs} @-}


-- * Logical predicates

{-@ measure sortedKeys @-}
sortedKeys :: Ord k => Assoc k v -> Bool
sortedKeys [] = True
sortedKeys ((k1,_):rest) = lowerBound k1 rest && sortedKeys rest

{-@ inline lowerBound @-}
lowerBound :: Ord k => k -> Assoc k v -> Bool
lowerBound _ [] = True
lowerBound k1 ((k2,_):_) = k1 < k2


-- * User API

{-@ merge :: _ -> Assoc k v -> Assoc k v -> Assoc k v @-}
merge :: Ord k => (v -> v -> v) -> Assoc k v -> Assoc k v -> Assoc k v
merge _ a [] = a
merge _ [] b = b
merge f a@(aHead@(aKey,aVal):aRest) b@(bHead@(bKey,bVal):bRest)
    | aKey == bKey  = (aKey, f aVal bVal) : merge f aRest bRest `withProof` proofLowerBoundUnchangedByMerge aKey f aRest bRest
--  | aKey <  bKey  = let rec = merge f aRest b in if lowerBound aHead rec then aHead : rec else undefined
    | aKey <  bKey  = aHead : merge f aRest b `withProof` proofLowerBoundUnchangedByMerge aKey f aRest b
    | otherwise     = bHead : merge f a bRest `withProof` proofLowerBoundUnchangedByMerge bKey f a bRest
{-@ reflect merge @-}


-- * Proofs

-- | Copied from "liquid-prelude:Language.Haskell.Liquid.ProofCombinators"
{-@ withProof :: x:a -> Proof -> {v:a | v = x} @-}
withProof :: a -> Proof -> a
withProof x _ = x
{-@ inline withProof @-}

{-@ proofEmptyIsSorted :: {sortedKeys []} @-}
proofEmptyIsSorted :: Proof
proofEmptyIsSorted = () *** QED
{-@ ple proofEmptyIsSorted @-}

{-@ proofEmptyIsSorted' :: {xs:_ | len xs == 0} -> {sortedKeys xs} @-}
proofEmptyIsSorted' :: Assoc k v -> Proof
proofEmptyIsSorted' [] = () *** QED
proofEmptyIsSorted' [_] = impossible "len is 0"
proofEmptyIsSorted' (_:_) = impossible "len is 0"

{-@ proofSingletonIsSorted :: {xs:_ | len xs == 1} -> {sortedKeys xs} @-}
proofSingletonIsSorted :: Assoc k v -> Proof
proofSingletonIsSorted [] = impossible "len is 1"
proofSingletonIsSorted [_] = () *** QED
proofSingletonIsSorted (_:_) = impossible "len is 1"

{-@ propPatternMatchRestIsSorted :: Assoc k v -> Assoc k v @-}
propPatternMatchRestIsSorted :: Assoc k v -> Assoc k v
propPatternMatchRestIsSorted [] = []
propPatternMatchRestIsSorted (_:xs) = xs

{-@
proofLowerBoundUnchangedByMerge
    :: lb:k
    -> f:(v -> v -> v)
    -> {xs:Assoc k v | lowerBound lb xs}
    -> {ys:Assoc k v | lowerBound lb ys}
    -> {lowerBound lb (merge f xs ys)}
@-}
proofLowerBoundUnchangedByMerge :: Ord k => k -> (v -> v -> v) -> Assoc k v -> Assoc k v -> Proof
proofLowerBoundUnchangedByMerge _ _ [] _ = () *** QED
proofLowerBoundUnchangedByMerge _ _ _ [] = () *** QED
proofLowerBoundUnchangedByMerge _ _ ((aKey,_):_) ((bKey,_):_)
    | aKey == bKey  = () *** QED
    | aKey <  bKey  = () *** QED
    | otherwise     = () *** QED
{-@ ple proofLowerBoundUnchangedByMerge @-}


-- * Todo

-- {-@
-- m
--     :: Assoc pid {i:Int | 0 < i}
--     -> Assoc pid {i:Int | 0 < i}
--     -> Assoc pid {i:Int | 0 < i} @-}
-- m :: Ord pid => Assoc pid Int -> Assoc pid Int -> Assoc pid Int
-- m xs ys = merge (+) xs ys

-- {-@
-- merge :: forall <p :: v -> Bool>.
--     (v<p> -> v<p> -> v<p>) -> Assoc k v<p> -> Assoc k v<p> -> Assoc k v<p>
-- @-}

-- {-@
-- proofValuePredMaintained
--     :: p:(v -> Bool)
--     -> f:({x:v | p x} -> {x:v | p x} -> {x:v | p x})
--     -> {xs:Assoc k v | valuesSatisfy p xs}
--     -> {ys:Assoc k v | valuesSatisfy p ys}
--     -> {valuesSatisfy p (merge f xs ys)}
-- @-}
-- proofValuePredMaintained :: Ord k => (v -> Bool) -> (v -> v -> v) -> Assoc k v -> Assoc k v -> Proof
-- proofValuePredMaintained _ _ [] _ = () *** QED
-- proofValuePredMaintained _ _ _ [] = () *** QED
-- proofValuePredMaintained p f ((aKey,aVal):_) ((bKey,bVal):_)
--     | aKey == bKey  = p (f aVal bVal) *** QED
--     | aKey <  bKey  = () *** Admit
--     | otherwise     = () *** Admit
-- {-@ ple proofValuePredMaintained @-}
