module Causal.CBCAST where

-- | Sorted list.
{-@ type Sorted a = [a]<{\x y -> x <= y}> @-}



-- | Verified insertion to a sorted list.
{-@
insertBeyond ::          a -> Sorted a -> Sorted a @-}
insertBeyond :: Ord a => a -> [a]      -> [a]
insertBeyond a [] = [a]
insertBeyond a (x:xs)
    | x <= a = x : insertBeyond a xs
    | otherwise = a : x : xs
{-@ reflect insertBeyond @-}
{-@
prop_insertBeyond :: {v:_ | v} @-}
prop_insertBeyond :: Bool
prop_insertBeyond = insertBeyond 2 [1,2,3] == [1,2,2,3::Int]



-- | Association, sorted association, and strictly-sorted association lists.
type                   Assoc k v = [(k, v)]
{-@ type         SortedAssoc k v = (Assoc k v)<{\a b -> fst a <= fst b}> @-} -- INCORRECT
{-@ type StrictlySortedAssoc k v = (Assoc k v)<{\a b -> fst a <  fst b}> @-} -- INCORRECT



-- | Verified insertion to sorted association-list, with duplicate keys being
-- inserted ahead of the streak of keys to which they compare equal.
{-@
insertAssocAhead ::          (k,v) -> SortedAssoc k v -> SortedAssoc k v @-}
insertAssocAhead :: Ord k => (k,v) ->       Assoc k v ->       Assoc k v
insertAssocAhead new@(newK,_) assoc = case assoc of
    []                  -> new : []
    cur@(curK,_) : rest
         | curK <= newK -> cur : insertAssocAhead new rest
         | otherwise    -> new : cur : rest
{-@ reflect insertAssocAhead @-}
{-@
test_insertAssocAhead ::         a -> a -> a -> a -> {v:_ | v} @-}
test_insertAssocAhead :: Eq a => a -> a -> a -> a -> Bool
test_insertAssocAhead a b b2 c = insertAssocAhead ('b',b2) [('a',a), ('b',b), ('c',c)] == [('a',a), ('b',b), ('b',b2), ('c',c)]



-- | Verified insertion to a sorted association-list, with duplicate keys being
-- inserted beyond the streak of keys to which they compare equal.
{-@
insertAssocBeyond ::          (k,v) -> SortedAssoc k v -> SortedAssoc k v @-}
insertAssocBeyond :: Ord k => (k,v) ->       Assoc k v ->       Assoc k v
insertAssocBeyond new@(newK,_) assoc = case assoc of
    []                  -> new : []
    cur@(curK,_) : rest
         | curK <= newK -> cur : insertAssocBeyond new rest
         | otherwise    -> new : cur : rest
{-@ reflect insertAssocBeyond @-}
{-@
test_insertAssocBeyond ::         a -> a -> a -> a -> {v:_ | v} @-}
test_insertAssocBeyond :: Eq a => a -> a -> a -> a -> Bool
test_insertAssocBeyond a b b2 c = insertAssocBeyond ('b',b2) [('a',a), ('b',b), ('c',c)] == [('a',a), ('b',b), ('b',b2), ('c',c)]



-- | Verified insertion into a sorted association-list, where duplicate keys'
-- values are combined into one value.
-- 
-- How is this different from the lh demo that failed to check?
-- <http://goto.ucsd.edu:8090/index.html#?demo=permalink%2F1607391843_24082.hs>
{-@
insertOrCombineAssoc ::          (v -> v -> v) -> (k,v) -> SortedAssoc k v -> SortedAssoc k v @-}
insertOrCombineAssoc :: Ord k => (v -> v -> v) -> (k,v) ->       Assoc k v ->       Assoc k v
insertOrCombineAssoc (~~) new@(newK,newV) assoc = case assoc of
    []                     -> new               : []
    cur@(curK,curV) : rest
            | curK <  newK -> cur               : insertOrCombineAssoc (~~) new rest
            | curK == newK -> (curK,newV~~curV) : rest
            | otherwise    -> new : cur         : rest
{-@ reflect insertOrCombineAssoc @-}
{-@
test_insertOrCombineAssoc ::                        a -> a -> a -> a -> {v:_ | v} @-}
test_insertOrCombineAssoc :: (Eq a, Semigroup a) => a -> a -> a -> a -> Bool
test_insertOrCombineAssoc a b b2 c = insertOrCombineAssoc (<>) ('b',b2) [('a',a), ('b',b), ('c',c)] == [('a',a), ('b',b2<>b), ('c',c)]



-- | Verified insertion into a sorted association-list, where duplicate keys'
-- values are combined into one value.
--
-- 1. The cases are swapped around to match the failing example.
{-@
insertOrCombineAssoc2 ::          (v -> v -> v) -> (k,v) -> SortedAssoc k v -> SortedAssoc k v @-}
insertOrCombineAssoc2 :: Ord k => (v -> v -> v) -> (k,v) ->       Assoc k v ->       Assoc k v
insertOrCombineAssoc2 (~~) new@(newK, newV) assoc = case assoc of
    []                      -> new               : []
    cur@(curK, curV) : rest
             | newK <  curK -> new : cur         : rest
             | newK == curK -> (curK,newV~~curV) : rest
             | otherwise    -> cur               : insertOrCombineAssoc2 (~~) new rest
{-@ reflect insertOrCombineAssoc2 @-}
{-@
test_insertOrCombineAssoc2 ::                        a -> a -> a -> a -> {v:_ | v} @-}
test_insertOrCombineAssoc2 :: (Eq a, Semigroup a) => a -> a -> a -> a -> Bool
test_insertOrCombineAssoc2 a b b2 c = insertOrCombineAssoc2 (<>) ('b',b2) [('a',a), ('b',b), ('c',c)] == [('a',a), ('b',b2<>b), ('c',c)]



-- | Verified insertion into a strictly-sorted association-list, where
-- duplicate keys' values are combined into one value.
--
-- 1. The cases are swapped around to match the failing example.
-- 2. The association list is strictly sorted.
{-@
insertOrCombineStrictAssoc2 ::          (v -> v -> v) -> (k,v) -> StrictlySortedAssoc k v -> StrictlySortedAssoc k v @-}
insertOrCombineStrictAssoc2 :: Ord k => (v -> v -> v) -> (k,v) ->               Assoc k v ->               Assoc k v
insertOrCombineStrictAssoc2 (~~) new@(newK, newV) assoc = case assoc of
    []                      -> new               : []
    cur@(curK, curV) : rest
             | newK <  curK -> new : cur         : rest
             | newK == curK -> (curK,newV~~curV) : rest
             | otherwise    -> cur               : insertOrCombineStrictAssoc2 (~~) new rest
{-@ reflect insertOrCombineStrictAssoc2 @-}
{-@
test_insertOrCombineStrictAssoc2 ::                        a -> a -> a -> a -> {v:_ | v} @-}
test_insertOrCombineStrictAssoc2 :: (Eq a, Semigroup a) => a -> a -> a -> a -> Bool
test_insertOrCombineStrictAssoc2 a b b2 c = insertOrCombineStrictAssoc2 (<>) ('b',b2) [('a',a), ('b',b), ('c',c)] == [('a',a), ('b',b2<>b), ('c',c)]



-- | Verified insertion into a strictly-sorted association-list, where
-- duplicate keys' values are combined into one value.
--
-- 1. The cases are swapped around to match the failing example.
-- 2. The association list is strictly sorted.
-- 3. The combine function is not passed in as argument.
{-@
insertOrCombineStrictAssoc2Semigroup ::                         (k,v) -> StrictlySortedAssoc k v -> StrictlySortedAssoc k v @-}
insertOrCombineStrictAssoc2Semigroup :: (Ord k, Semigroup v) => (k,v) ->               Assoc k v ->               Assoc k v
insertOrCombineStrictAssoc2Semigroup new@(newK, newV) assoc = case assoc of
    []                      -> new               : []
    cur@(curK, curV) : rest
             | newK <  curK -> new : cur         : rest
             | newK == curK -> (curK,newV<>curV) : rest
             | otherwise    -> cur               : insertOrCombineStrictAssoc2Semigroup new rest
-- {-@ reflect insertOrCombineStrictAssoc2Semigroup @-}

-- {-@
-- test_insertOrCombineStrictAssoc2Semigroup :: {v:_ | v} @-}
test_insertOrCombineStrictAssoc2Semigroup :: Bool
test_insertOrCombineStrictAssoc2Semigroup = insertOrCombineStrictAssoc2Semigroup ('b',"z") [('a',"a"), ('b',"b"), ('c',"c")] == [('a',"a"), ('b',"zb"), ('c',"c")]

-- {-@
-- egSA :: StrictlySortedAssoc Char Int @-}
-- egSA ::               Assoc Char Int
-- egSA = [('a',1)]
