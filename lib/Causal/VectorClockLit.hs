module Causal.VectorClockLit where


-- * Types

type Clock = Integer
{-@ type     Clock = {c:Integer | cMin  <= c} @-}
{-@ type RealClock = {c:Integer | rcMin <= c} @-}

data VCAssoc pid
    = Nil
    | VC pid Clock (VCAssoc pid)
    deriving (Eq)
{-@
data VCAssoc [vcSize] pid
    = Nil
    | VC
        { p :: pid
        , c :: RealClock
        , r :: VCAssoc {p':pid | p < p'}
        }
@-}


-- * Clock values

-- | Clocks range on [0..∞) because vector clocks count ticks, but a pid might
-- not have ticked yet. This is the returned type.
{-@ inline cMin @-}
{-@ cMin :: Clock @-}
cMin :: Clock
cMin = 0

-- | RealClocks range on [1..∞) because vector clocks count ticks, and after
-- the first 'vcTick' of a pid the clock counts one tick. This is the stored
-- type.
{-@ inline rcMin @-}
{-@ rcMin :: RealClock @-}
rcMin :: Clock
rcMin = 1


-- * Logical predicates

{-@ measure vcSize @-}
{-@ vcSize :: VCAssoc pid -> Nat @-}
vcSize :: VCAssoc pid -> Int
vcSize Nil = 0
vcSize (VC _ _ vc) = 1 + vcSize vc

{-@ inline larger @-}
larger :: Ord a => a -> a -> a
larger a b = if a < b then b else a


-- * User API 

{-@ inline vcNew @-}
vcNew :: VCAssoc pid
vcNew = Nil

{-@ reflect vcTick @-}
vcTick :: Ord pid => pid -> VCAssoc pid -> VCAssoc pid
vcTick pid Nil      = {- nil  -} VC pid rcMin Nil
vcTick pid (VC cur clock rest)
    | pid <  cur    = {-insert-} VC pid rcMin (VC cur clock rest)
    | pid == cur    = {-update-} VC cur (clock+1) rest
    | otherwise     = {-search-} VC cur clock (vcTick pid rest)

{-@ reflect vcRead @-}
{-@ vcRead :: _ -> _ -> Clock @-}
vcRead :: Ord pid => pid -> VCAssoc pid -> Clock
vcRead _ Nil = cMin
vcRead pid (VC cur clock rest)
    | pid == cur    = clock
    | otherwise     = vcRead pid rest

{-@ reflect vcCombine @-}
{-@ vcCombine :: a:_ -> b:_ -> _ / [vcSize a + vcSize b] @-}
vcCombine :: Ord pid => VCAssoc pid -> VCAssoc pid -> VCAssoc pid
vcCombine x   Nil   = {- x&nil -} x
vcCombine Nil y     = {- nil&y -} y
vcCombine (VC xPid xClock xRest) (VC yPid yClock yRest)
    | xPid <  yPid  = {-x-ahead-} VC xPid  xClock                  (vcCombine xRest (VC yPid yClock yRest))
    | xPid == yPid  = {-combine-} VC xPid (xClock `larger` yClock) (vcCombine xRest yRest)
    | otherwise     = {-y-ahead-} VC yPid                  yClock  (vcCombine (VC xPid xClock xRest) yRest)

{-@ reflect vcLessEqual @-}
{-@ vcLessEqual :: a:_ -> b:_ -> _ / [vcSize a + vcSize b] @-}
vcLessEqual :: Ord pid => VCAssoc pid -> VCAssoc pid -> Bool
vcLessEqual Nil Nil                 = {- equal  -} True
vcLessEqual (VC _ xClock xRest) Nil = {- x<=nil -} xClock <= cMin   {-False-} && vcLessEqual xRest Nil
vcLessEqual Nil (VC _ yClock yRest) = {- nil<=y -} cMin   <= yClock {-True -} && vcLessEqual Nil yRest
vcLessEqual x@(VC xPid xClock xRest) y@(VC yPid yClock yRest)
    | xPid <  yPid  = {-x-ahead-} xClock <= cMin   {-False-} && vcLessEqual xRest y
    | xPid == yPid  = {-compare-} xClock <= yClock           && vcLessEqual xRest yRest
    | otherwise     = {-y-ahead-} cMin   <= yClock {-True -} && vcLessEqual x     yRest

{-@ inline vcLess @-}
vcLess :: Ord pid => VCAssoc pid -> VCAssoc pid -> Bool
vcLess a b = vcLessEqual a b && a /= b

{-@ inline vcIndependent @-}
vcIndependent :: Ord pid => VCAssoc pid -> VCAssoc pid -> Bool
vcIndependent a b = not (vcLess a b) && not (vcLess b a)
