module Containers3 where

-- EXAMPLE FROM @pzp HERE
-- https://liquidhaskell.slack.com/archives/C54QAL9RR/p1601612833076000?thread_ts=1601612338.073600&cid=C54QAL9RR

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

fooSize :: FooT -> Int
fooSize (FooC xs) = listLen xs
{-@ LIQUID "--exact-data-cons" @-}
{-@ reflect fooSize @-}

{-@
_a :: _ -> {b:_ | b == True } @-}
_a :: FooT -> Bool
_a f = fooSize f == listLen (field f)
