module Foo where

-- import Control.Arrow (first)
-- {-@ crash :: {x:_ | x == True } @-}
-- crash :: Bool
-- crash = const True (first id)

-------------------------------------------------
--
-- DOES REFINING A DATATYPE MAKE MEASURES?

-- http://ucsd-progsys.github.io/liquidhaskell/options/#no-measure-fields
--      "When a data type is refined, Liquid Haskell automatically turns the
--      data constructor fields into measures."

{-@
data FooT = FooC { fooField :: Int } @-}
data FooT = FooC { fooField :: Int }

{-@
fooField2 :: a:_ -> {b:_ | b == fooField a} @-}
fooField2 :: FooT -> Int
fooField2 (FooC i) = let f = FooC i in fooField f
{-@ measure fooField2 @-}

{-@
fooIsContainer :: a:_ -> {b:_ | a == b } @-}
fooIsContainer :: Int -> Int
fooIsContainer i = fooField (FooC i)

-------------------------------------------------
--
-- CAN YOU MANUALLY DEFINE MEASURES FOR FIELDS?

data BarT = BarC { barField :: Int }
{-@ measure barField @-}

{-@
barField2 :: a:_ -> {b:_ | b == barField a} @-}
barField2 :: BarT -> Int
barField2 (BarC i) = let b = BarC i in barField b
{-@ measure barField2 @-}

{-@
barIsContainer :: a:_ -> {b:_ | a == b } @-}
barIsContainer :: Int -> Int
barIsContainer i = barField (BarC i)

-----------------------------------------------------
