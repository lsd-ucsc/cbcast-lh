
-- | Standard library things reimplemented and reflected.
module Redefined where




-- * Ord

-- | Implementation of 'max' lifted to specifications.
--
-- prop> max a b == ordMax a b
ordMax :: Ord a => a -> a -> a
ordMax x y = if x < y then y else x
{-@ reflect ordMax @-}




-- * Vec and Fin

-- | A list of fixed size. (Agda's Vec)
{-@ type Vec a V = {v:[a] | len v == V} @-}
type Vec a = [a]

-- | A member of a finite set of natural numbers. (Agda's Fin)
{-@ type Fin V = {k:Nat | k < V} @-}
type Fin = Int

-- | A whole finite set in descending/ascending order as a list.
{-@ type FinDesc N = {xs:[Fin {N}]<{\a b -> a > b}> | len xs == N} @-}
{-@ type FinAsc  N = {xs:[Fin {N}]<{\a b -> a < b}> | len xs == N} @-}

-- | Generate the elements of a finite set @Fin n@ in descending order
--
-- >>> finDesc (-1)
-- []
-- >>> finDesc 0
-- []
-- >>> finDesc 1
-- [0]
-- >>> finDesc 2
-- [1,0]
-- >>> finDesc 3
-- [2,1,0]
--
{-@ finDesc :: n:Nat -> FinDesc {n} @-}
finDesc :: Int -> [Int]
finDesc k = let k' = k - 1 in if 0 <= k' then k' : finDesc k' else []
{-@ reflect finDesc @-}

-- | Generate the elements of a finite set @Fin n@ in ascending order
--
-- >>> finAsc (-1)
-- []
-- >>> finAsc 0
-- []
-- >>> finAsc 1
-- [0]
-- >>> finAsc 2
-- [0,1]
-- >>> finAsc 3
-- [0,1,2]
--
{-@ finAsc :: n:Nat -> FinAsc {n} @-}
finAsc :: Int -> [Int]
finAsc n = finAscHelper 0 n
{-@ reflect finAsc @-}

-- | Returns bounded by [m..n) in ascending order.
--
-- >>> finAscHelper 4 9
-- [4,5,6,7,8]
--
{-@ finAscHelper
        ::  m:Nat
        -> {n:Nat | m <= n}
        -> {xs:[{x:_ | m <= x && x < n}]<{\a b -> a < b}> | len xs == n-m}
        / [n-m] @-}
finAscHelper :: Int -> Int -> [Int]
finAscHelper m n =
    if m < n
    then m : finAscHelper (m+1) n
    else []
{-@ reflect finAscHelper @-}




-- * List

cons :: a -> [a] -> [a]
cons x xs = x:xs
{-@ inline cons @-}

{-@ listLength :: xs:_ -> {v:Nat | v == len xs } @-}
listLength :: [a] -> Int
listLength [] = 0
listLength (_x:xs) = 1 + listLength xs
{-@ measure listLength @-}

listElem :: Eq a => a -> [a] -> Bool
listElem _ [] = False
listElem e (x:xs) = e==x || listElem e xs
{-@ reflect listElem @-}

listTailForHead :: Eq a => a -> [a] -> [a]
listTailForHead _ [] = []
listTailForHead e (x:xs) = if e==x then xs else listTailForHead e xs
{-@ reflect listTailForHead @-}

{-@ listIndex :: xs:[a] -> Fin {len xs} -> a @-}
listIndex :: [a] -> Int -> a
listIndex (x:xs) i = if i==0 then x else listIndex xs (i-1)
{-@ reflect listIndex @-}

listAnd :: [Bool] -> Bool
listAnd [] = True
listAnd (x:xs) = x && listAnd xs
{-@ reflect listAnd @-}

{-@ listZipWith :: _ ->  xs:_
                     -> {ys:_ | len xs == len ys}
                     -> {zs:_ |           len ys == len zs} @-}
listZipWith :: (a -> b -> c) -> [a] -> [b] -> [c]
listZipWith _ [] [] = []
listZipWith f (x:xs) (y:ys) = f x y : listZipWith f xs ys
{-@ reflect listZipWith @-}

{-@ listZipWith3 :: _ ->  ws:_
                      -> {xs:_ | len ws == len xs}
                      -> {ys:_ |           len xs == len ys}
                      -> {zs:_ |                     len ys == len zs} @-}
listZipWith3 :: (a -> b -> c -> d) -> [a] -> [b] -> [c] -> [d]
listZipWith3 _ [] [] [] = []
listZipWith3 f (x:xs) (y:ys) (z:zs) = f x y z : listZipWith3 f xs ys zs
{-@ reflect listZipWith3 @-}




-- * Unique lists

{-@ type UniqueList a = [a]<{\j k -> j /= k}> @-}

-- | Push evidence @not (listElem e xs)@ into the type parameter of @xs@ such
-- that the result is type @[{x:a | e /= x}]@.
{-@
uniqueListConsable
    :: e:a
    -> {xs:UniqueList a | not (listElem e xs)}
    -> {ys:UniqueList ({y:a | e /= y}) | xs == ys}
@-}
uniqueListConsable :: Eq a => a -> [a] -> [a]
uniqueListConsable _e [] = []
uniqueListConsable e (x:xs) = x : uniqueListConsable e xs
{-@ ple uniqueListConsable @-} -- e≠x ∧ ¬(e∈xs)
{-@ reflect uniqueListConsable @-}

{-@
uCons
    ::   e:a
    -> {xs:UniqueList a | not (listElem e xs)}
    -> {ys:UniqueList a | ys == cons e xs}
@-}
uCons :: Eq a => a -> [a] -> [a]
uCons e xs = e : uniqueListConsable e xs
{-@ reflect uCons @-}
