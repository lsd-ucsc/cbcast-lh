module Containers where

-- Either of these annotations are sufficient and produce the same outcome (field is a measure and FooC is a container).
{-@ measure field @-}
--{-@ data FooT = FooC { field :: Int } @-}
data FooT = FooC { field :: Int }

{-@
field2 :: f:_ -> {i:_ | i == field f} @-}
field2 :: FooT -> Int
field2 (FooC i) = let f = FooC i in field f -- Use of field in field2 proves that field is a measure if we can make field2 into a measure.
{-@ measure field2 @-}

{-@
fooIsContainer :: a:_ -> {b:_ | a == b } @-} -- This shows that liquidhaskell understands that FooC is a container and field is an extractor.
fooIsContainer :: Int -> Int
fooIsContainer i = field (FooC i)

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@
_p :: f:_ -> { field f == field2 f } @-}
_p :: FooT -> ()
_p (FooC _) = ()
