module Causal.VectorClockRefl where

-- Using uniqueness defined this way
-- https://ucsd-progsys.github.io/liquidhaskell-tutorial/Tutorial_08_Measure_Set.html

import qualified Data.Set as S -- Lifted: Set, empty, singleton, member, union, intersection, difference

-- import Language.Haskell.Liquid.ProofCombinators (Proof, (===), (***))
-- import qualified Language.Haskell.Liquid.ProofCombinators as Proof

type Clock = Integer
type VCList pid = [(pid, Clock)]

vclPids :: Ord pid => VCList pid -> S.Set pid
vclPids vcl = case vcl of
    [] -> S.empty
    (pid,_):rest -> S.singleton pid `S.union` vclPids rest
{-@ measure vclPids @-}

vclPidsUnique :: Ord pid => VCList pid -> Bool
vclPidsUnique vcl = case vcl of
    [] -> True
    (pid,_):rest -> not (S.member pid $ vclPids rest) && vclPidsUnique rest
{-@ measure vclPidsUnique @-}

{-@ type Clock = {c:Integer | 0 <= c} @-}
{-@ type RealClock = {c:Integer | 1 <= c} @-}
{-@ type VCList pid = {vcl:[(pid, RealClock)] | vclPidsUnique vcl} @-}

{-@ ok :: VCList Char @-}
ok :: VCList Char
ok = [('a',1), ('b',1), ('c',1)]

{-@ bad :: VCList Char @-}
bad :: VCList Char
bad = [('a',1), ('b',1), ('a',1)]
{-@ ignore bad @-}

-- Patrick: I think all of the representations we have tried have the same
-- problem: The recursive call does not preserve the fact needed by LH to do
-- cons, because that fact isn't present in the postcondition. The fix is to
-- reestablish that fact ahead of doing cons.

{-@ vclTick :: pid:pid -> xs:VCList pid -> {ys:VCList pid | vclPids ys == S.union (vclPids xs) (S.singleton pid)} @-}
vclTick :: (Eq pid, Ord pid) => pid -> VCList pid -> VCList pid
vclTick pid vcl = case vcl of
    []                  -> (pid,1):[]
    (cur,clock):rest
        | pid == cur    -> (cur,clock+1):rest
        | otherwise     -> (cur,clock):(vclTick pid rest)

-- Gan: could we first look up, and decide what to do?
{-@ vclTickPermission :: pid -> VCList pid -> VCList pid @-}
vclTickPermission :: (Eq pid, Ord pid) => pid -> VCList pid -> VCList pid
vclTickPermission pid vcl
    | S.member pid (vclPids vcl) = vclTickPermissionHelper pid vcl
    | otherwise = (pid,1):vcl
{-@ vclTickPermissionHelper :: p:pid -> xs:VCList pid -> {ys:VCList pid | vclPids xs == vclPids ys} @-}
vclTickPermissionHelper :: Eq pid => pid -> VCList pid -> VCList pid
vclTickPermissionHelper pid vcl = case vcl of
    []                  -> []
    (cur,clock):rest
        | pid == cur    -> (cur,clock+1):rest
        | otherwise     -> (cur,clock):vclTickPermissionHelper pid rest

-- Patrick: could we do this with a lemma?
{-@ vclTickViaLemma :: pid -> VCList pid -> VCList pid @-}
vclTickViaLemma :: (Eq pid, Ord pid) => pid -> VCList pid -> VCList pid
vclTickViaLemma pid vcl = case vcl of
    []                  -> (pid,1):[]
    (cur,clock):rest
        | pid == cur    -> (cur,clock+1):rest
        | otherwise     -> (cur,clock):vclTickViaLemma pid rest
                            `withProof` vclTickLemmaP cur pid rest
{-@ reflect vclTickViaLemma @-}
{-@ ple vclTickViaLemma @-}

{-@ notIn :: Ord pid => pid -> VCList pid -> Bool @-}
notIn :: Ord pid => pid -> VCList pid -> Bool
notIn pid vcl = not (S.member pid $ vclPids vcl)
{-@ reflect notIn @-}

{-@
vclTickLemmaP :: n:pid -> {p:pid | n /= p} -> {xs:VCList pid | notIn n xs}
    -> { notIn n (vclTickViaLemma p xs) }
@-}
vclTickLemmaP :: Ord pid => pid -> pid -> VCList pid -> Proof
vclTickLemmaP n pid [] = ()
vclTickLemmaP n pid ((cur,clock):rest)
    | pid == cur = ()
    | otherwise
        =   () -- notIn n ((cur,clock):vclTickViaLemma pid rest)
        *** Admit
{-@ reflect vclTickLemmaP @-}
{-@ ple vclTickLemmaP @-}


{-@ restTest :: VCList pid -> VCList pid @-}
restTest :: VCList pid -> VCList pid
restTest [] = []
restTest ((cur,clock):xs) = (cur,clock):xs
-- restTest (x:xs) = x:xs

{-@ cons :: p:pid -> RealClock -> {vcl:VCList pid | not (S.member p (vclPids vcl)) } -> VCList pid @-}
cons :: pid -> Clock -> VCList pid -> VCList pid
cons pid clock vcl = (pid,clock):vcl

-- * Proof combinators

type Proof = ()

data QED = Admit | QED

-- Gan: called "refl" in agda
{-@ (===) :: x:a -> y:{a | y == x} -> {v:a | v == x && v == y} @-}
(===) :: a -> a -> a
_ === y = y
infixl 3 ===
{-@ inline === @-}

{-@ assume (***) :: a -> p:QED -> { if p == Admit then false else true } @-}
(***) :: a -> QED -> Proof
_ *** _ = ()
infixl 3 ***
{-@ inline *** @-}

{-@ withProof :: x:a -> Proof -> {v:a | v = x} @-}
withProof :: a -> Proof -> a
withProof x _ = x
{-@ inline withProof @-}

