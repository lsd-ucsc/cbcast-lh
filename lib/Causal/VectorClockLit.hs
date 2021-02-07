module Causal.VectorClockLit where

-- * Types

type Clock = Integer
{-@ type Clock = {c:Integer | 0 <= c} @-}
{-@ type RealClock = {c:Integer | 1 <= c} @-}

data VCAssoc pid
    = Nil
    | VC pid Clock (VCAssoc pid)
{-@
data VCAssoc [vcSize] pid
    = Nil
    | VC
        { p :: pid
        , c :: RealClock
        , r :: VCAssoc {p':pid | p < p'}
        }
@-}


-- * Logical predicates

{-@ measure vcSize @-}
{-@ vcSize :: VCAssoc pid -> Nat @-}
vcSize :: VCAssoc pid -> Int
vcSize Nil = 0
vcSize (VC _ _ vc) = 1 + vcSize vc

-- |
--
-- >>> larger 1 2
-- 2
-- >>> larger 2 1
-- 2
{-@ inline larger @-}
larger :: Ord a => a -> a -> a
larger a b = if a > b then a else b


-- * User API 

{-@ inline vcNew @-}
vcNew :: VCAssoc pid
vcNew = Nil

{-@ reflect vcTick @-}
vcTick :: Ord pid => pid -> VCAssoc pid -> VCAssoc pid
vcTick pid Nil      = {-nil   -} VC pid 1 Nil
vcTick pid (VC cur clock rest)
    | pid <  cur    = {-insert-} VC pid 1 $ VC cur clock rest
    | pid == cur    = {-update-} VC cur (clock+1) rest
    | otherwise     = {-search-} VC cur clock $ vcTick pid rest

{-@ vcCombine :: a:_ -> b:_ -> _ / [vcSize a + vcSize b] @-}
vcCombine :: Ord pid => VCAssoc pid -> VCAssoc pid -> VCAssoc pid
vcCombine x   Nil   = {- x&nil -} x
vcCombine Nil y     = {- nil&y -} y
vcCombine (VC xPid xClock xRest) (VC yPid yClock yRest)
    | xPid <  yPid  = {-x-ahead-} VC xPid xClock                   (vcCombine xRest (VC yPid yClock yRest))
    | xPid == yPid  = {-combine-} VC xPid (xClock `larger` yClock) (vcCombine xRest yRest)
    | otherwise     = {-y-ahead-} VC yPid yClock                   (vcCombine (VC xPid xClock xRest) yRest)

{-@ vcLessEqual :: a:_ -> b:_ -> _ / [vcSize a + vcSize b] @-}
vcLessEqual :: Ord pid => VCAssoc pid -> VCAssoc pid -> Bool
vcLessEqual Nil Nil                 = {- equal  -} True
vcLessEqual (VC _ xClock xRest) Nil = {- x<=nil -} xClock <= 0      {-False-} && vcLessEqual xRest Nil
vcLessEqual Nil (VC _ yClock yRest) = {- nil<=y -} 0      <= yClock {-True -} && vcLessEqual Nil yRest
vcLessEqual x@(VC xPid xClock xRest) y@(VC yPid yClock yRest)
    | xPid <  yPid  = {-x-ahead-} xClock <= 0      {-False-} && vcLessEqual xRest y
    | xPid == yPid  = {-compare-} xClock <= yClock           && vcLessEqual xRest yRest
    | otherwise     = {-y-ahead-} 0      <= yClock {-True -} && vcLessEqual x     yRest
