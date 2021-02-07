module SortedConsecutive where

type Assoc k v = [(k, v)]

-- lessThanHead :: Ord k => k -> Assoc k v -> Bool
-- lessThanHead _ [] = True
-- lessThanHead k ((k',_):_) = k < k'
-- {-@ reflect lessThanHead @-}
-- 
-- sorted :: Ord k => Assoc k v -> Bool
-- sorted [] = True
-- sorted ((k,_):rest) = lessThanHead k rest && sorted rest
-- {-@ measure sorted @-}

sorted :: Ord k => Assoc k v -> Bool
sorted assoc = case assoc of
    (k1,_):rest@((k2,_):_) -> k1 < k2 && sorted rest
    _ -> True
{-@ reflect sorted @-}

{-@ type Assoc k v = {xs:[(k, v)] | sorted xs} @-}

{-@ propPatternMatchRestIsSorted :: Assoc k v -> Assoc k v @-}
propPatternMatchRestIsSorted :: Assoc k v -> Assoc k v
propPatternMatchRestIsSorted [] = []
propPatternMatchRestIsSorted (_:xs) = xs
