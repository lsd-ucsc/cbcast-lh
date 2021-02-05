module Causal.VectorClockGhost where

-- * Ranjit's example for a sorted list with a lower bound

{-
{-@ type OAssocLB k v LB = [{tup:(k, v) | LB < fst tup}]<{\i1 i2 -> fst i1 < fst i2}> @-}

{-@ ins :: lb:k -> ({newK:k| lb < newK} , v) -> OAssocLB k v lb -> OAssocLB k v lb @-}
ins :: (Ord k, Semigroup v) => k -> (k, v) -> [(k, v)] -> [(k, v)]
ins lb (newK, newV) assoc = case assoc of
    []                  -> [(newK, newV)]
    (curK, curV) : rest
        | newK <  curK  -> (newK, newV) : (curK, curV) : rest
        | newK == curK  -> (curK, newV <> curV) : rest
        | newK >  curK  -> (curK, curV) : ins curK (newK, newV) rest
--}


-- * Attempts to define a VC similarly

type Clock = Integer
{-@ type     Clock = {c:Integer | 0 <= c} @-}
{-@ type RealClock = {c:Integer | 1 <= c} @-}

type VCList pid = [(pid, Clock)]
{-@ type VCList   pid    = [   (pid, RealClock)               ]<{\a b -> fst a /= fst b}> @-}
{-@ type VCListNK pid NK = [{t:(pid, RealClock) | NK /= fst t}]<{\a b -> fst a /= fst b}> @-}

{-@ ok :: VCList Char @-}
ok :: VCList Char
ok = [('a',1), ('b',1), ('c',1)]

{-@ bad :: VCList Char @-}
bad :: VCList Char
bad = [('a',1), ('b',1), ('a',1)]
{-@ ignore bad @-}

{-@ ignore vcTickBroken @-}
{-@ vcTickBroken :: pid -> VCList pid -> VCList pid @-}
vcTickBroken :: Eq pid => pid -> VCList pid -> VCList pid
vcTickBroken pid vcl = case vcl of
    []                  -> (pid,1):[]
    (cur,clock):rest
        | pid == cur    -> (cur,clock+1):rest
                        -- LH knows that cur is not in rest. That fact is lost
                        -- in the recursive call. So we cannot use cons.
        | otherwise     -> (cur,clock):vcTickBroken pid rest

{-@ vcTickNK :: nk:pid -> {p:pid | nk /= p} -> VCListNK pid nk -> VCListNK pid nk @-}
vcTickNK :: Eq pid => pid -> pid -> VCList pid -> VCList pid
vcTickNK _ pid vcl = case vcl of
    []                  -> (pid,1):[]
    (cur,clock):rest
        | pid == cur    -> (cur,clock+1):rest
                        -- LH knows that cur is not in rest. That fact is
                        -- maintained in the recursive call. So we can use
                        -- cons.
        | otherwise     -> undefined -- (cur,clock):vcTickNK cur pid rest

{-@ vcTick :: pid -> VCList pid -> VCList pid @-}
vcTick :: Eq pid => pid -> VCList pid -> VCList pid
vcTick pid vcl = case vcl of
    []                  -> (pid,1):[]
    (cur,clock):rest
        | pid == cur    -> (cur,clock+1):rest
                        -- LH knows that cur is not in rest. We can call
                        -- vcTickNK.
        | otherwise     -> (cur,clock):vcTickNK cur pid rest
