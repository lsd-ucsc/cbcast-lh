module SortedPairwise where

type Assoc k v = [(k, v)]

lessThanAll :: Ord k => k -> Assoc k v -> Bool
lessThanAll _ [] = True
lessThanAll k ((k',_):rest) = k < k' && lessThanAll k rest
{-@ reflect lessThanAll @-}

sorted :: Ord k => Assoc k v -> Bool
sorted [] = True
sorted ((k,_):rest) = lessThanAll k rest && sorted rest
{-@ measure sorted @-}

{-@ type Assoc k v = {xs:[(k, v)] | sorted xs} @-}

{-@ propPatternMatchRestIsSorted :: Assoc k v -> Assoc k v @-}
propPatternMatchRestIsSorted :: Assoc k v -> Assoc k v
propPatternMatchRestIsSorted [] = []
propPatternMatchRestIsSorted (_:xs) = xs
