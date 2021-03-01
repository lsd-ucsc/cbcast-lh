-- |
--
-- These are definitions redefined from elsewhere for use with LiquidHaskell.
module Redefined where

-- $setup
-- >>> :set -XFlexibleInstances
-- >>> instance Show (a -> b) where show _ = "(a -> b)"
-- >>> import Data.List


-- * Haskell things reimplemented

-- | Reify the @len@ measure defined in the @liquid-base@ specification into
-- code and back into specifications.
--
-- prop> length xs == listLength xs
{-@
listLength :: xs:_ -> {v:Nat | v == len xs } @-}
listLength :: [a] -> Int
listLength [] = 0
listLength (_x:xs) = 1 + listLength xs
{-@ measure listLength @-}

-- | Implementation of 'and' lifted to specifications. Probably same as
-- 'Prelude'.
--
-- prop> and xs == listAnd xs
{-@ reflect listAnd @-} -- FIXME: this causes a crash when it's a measure?
listAnd :: [Bool] -> Bool
listAnd [] = True
listAnd (b:bs) = b && listAnd bs

-- | Implementation of 'replicate' lifted to specifications. Probably same as
-- that of 'Prelude'.
--
-- prop> replicate n x == listReplicate n x
{-@ reflect listReplicate @-}
{-@ listReplicate :: n:Nat -> item:a -> {xs:[{x:a | x == item}] | n == listLength xs} @-}
listReplicate :: Int -> a -> [a]
listReplicate n x
    | n <= 0    = []
    | otherwise = x:listReplicate (n-1) x

{-@ reflect boolAnd @-}
{-@ boolAnd :: a:Bool -> b:Bool -> {c:Bool | c <=> a && b} @-}
boolAnd :: Bool -> Bool -> Bool
boolAnd True True = True
boolAnd _ _ = False

-- | Implementation of 'map' lifted to specifications. Probably same as
-- 'Prelude'.
--
-- prop> map f xs == listMap f xs
{-@ reflect listMap @-}
listMap :: (a -> b) -> [a] -> [b]
listMap f (x:xs) = f x:listMap f xs
listMap _ [] = []

-- | Implementation of 'foldl' lifted to specifications. Probably same as
-- 'Prelude'.
--
-- prop> foldl f acc xs == listFoldl f acc xs
{-@ reflect listFoldl @-}
listFoldl :: (b -> a -> b) -> b -> [a] -> b
listFoldl f acc (x:xs) = listFoldl f (f acc x) xs
listFoldl _ acc [] = acc

-- | Implementation of 'reverse' lifted to specifications. Copied from
-- 'Prelude'.
--
-- prop> reverse xs == listReverse xs
{-@
listReverse :: xs:_ -> {ys:_ | listLength xs == listLength ys} @-}
listReverse :: [a] -> [a]
listReverse orig = listReverseImpl orig []
{-@ inline listReverse @-}

{-@
listReverseImpl :: xs:_ -> ys:_ -> {zs:_ | listLength xs + listLength ys == listLength zs} @-}
listReverseImpl :: [a] -> [a] -> [a]
listReverseImpl []     done = done
listReverseImpl (x:xs) done = listReverseImpl xs (x:done)
{-@ reflect listReverseImpl @-}

-- | Similar to @base:Data.List.elemIndex@ or
-- @containers:Data.Sequence.elemeIndexL@, "elemIndexL finds the leftmost index
-- of the specified element, if it is present, and otherwise Nothing," but is
-- implemented more simply.
--
-- prop> elemIndex a xs == listElemIndex a xs
{-@
listElemIndex :: x:_ -> xs:_ -> {m:_ | listElem x xs => isJust m} @-}
listElemIndex :: Eq a => a -> [a] -> Maybe Int
listElemIndex a xs = listElemIndexImpl a xs 0
{-@ inline listElemIndex @-}

{-@
listElemIndexImpl :: x:_ -> xs:_ -> _ -> {m:_ | listElem x xs => isJust m} @-}
listElemIndexImpl :: Eq a => a -> [a] -> Int -> Maybe Int
listElemIndexImpl _ [] _ = Nothing
listElemIndexImpl a (x:xs) idx
    | a == x = Just idx
    | otherwise = listElemIndexImpl a xs (idx + 1)
{-@ reflect listElemIndexImpl @-}
{-@ ple listElemIndexImpl @-}

-- | Implementation of 'elem' lifted to specifications. Copied from 'Prelude'.
--
-- prop> elem a xs == listElem a xs
listElem :: Eq a => a -> [a] -> Bool
listElem _ []     = False
listElem x (y:ys) = x==y || listElem x ys
{-@ reflect listElem @-}

-- | Implementation of 'init' combined with 'last' lifted to specifications.
--
-- prop> not (null xs) ==> (init xs, last xs) == listInitLast xs
{-@ reflect listInitLast @-}
{-@ listInitLast :: {xs:[a] | 0 < len xs} -> ([a], a) @-}
listInitLast :: [a] -> ([a], a)
listInitLast [x] = ([], x)
listInitLast (a:b:cs) = let (xs, x) = listInitLast (b:cs) in (a:xs, x)

-- | Implementation of 'flip' lifted to specifications. Probably same as
-- 'Prelude'.
--
-- prop> f a b == flip f b a && flip f b a == funFlip f b a
{-@ reflect funFlip @-}
funFlip :: (a -> b -> c) -> b -> a -> c
funFlip f b a = f a b

-- | Implementation of 'impossible' lifted to specifications. similar to the
-- one in 'Language.Haskell.Liquid.ProofCombinators'.
{-@ inline impossibleConst @-}
{-@ impossibleConst :: a -> {v:b | false } -> a @-}
impossibleConst :: a -> b -> a
impossibleConst a _ = a


-- * Agda things reimplemented

-- | A list of fixed size.
{-@ type Vec a V = {v:[a] | len v == V} @-}
type Vec a = [a]

-- | A member of a finite set of natural numbers.
{-@ type Fin V = {k:Nat | k < V} @-}
type Fin = Int

-- | Generate the elements of a finite set @Fin n@.
--
-- >>> fin (-1)
-- []
-- >>> fin 0
-- []
-- >>> fin 1
-- [0]
-- >>> fin 2
-- [1,0]
--
{-@ reflect fin @-}
{-@ fin :: v:Nat -> {xs:[Fin {v}]<{\a b -> a > b}> | len xs == v} @-}
fin :: Int -> [Int]
fin k = let k' = k - 1 in if 0 < k then k' : fin k' else []

-- | Lookup an element of a non-empty list given a valid index. This is called
-- "lookup" in agda and "!!" or "genericIndex" in haskell.
--
-- prop> 0 <= i && i < length xs ==> xs !! i == listIndex xs i
{-@ reflect listIndex @-}
{-@ listIndex :: xs:[a] -> Fin {len xs} -> a @-}
listIndex :: [a] -> Int -> a
listIndex (x:xs) i
    | i == 0    = x
    | otherwise = listIndex xs (i-1)
