module Containers2 where

-- DO YOU HAVE TO REPEAT THE MEASURE IMPL IN ITS TYPE?
-- YES, if you use measure
-- NO, see Containers3

{-@
listLen :: _ -> Nat @-}
listLen :: [a] -> Int
listLen [] = 0
listLen (_:xs) = 1 + listLen xs
{-@ measure listLen @-}

{-@
data FooT [fooSize]
          = FooC { field :: String } @-}
data FooT = FooC { field :: String }

-- {-@ fooSize :: _ -> Nat @-} -- Why is this simpler type insufficient to check _a, below? It seems odd to repeat the entire implementation of fooSize in the refinement type!
{-@ fooSize :: f:_ -> {n:Nat | n == listLen (field f)} @-}
fooSize :: FooT -> Int
fooSize (FooC xs) = listLen xs
{-@ measure fooSize @-}

{-@
_a :: _ -> {b:_ | b == True } @-}
_a :: FooT -> Bool
_a f = fooSize f == listLen (field f)
