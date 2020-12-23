{-# LANGUAGE LambdaCase #-}
module Eg1 where

{-@
data Foo = Foo Int @-}
data Foo = Foo Int

lessEq :: Foo -> Foo -> Bool
lessEq (Foo a) (Foo b) = a <= b
{-@ inline lessEq @-}

data List a
    = Nil
    | Cons a (List a)
{-@
data List a where
      Nil  ::                                     List a
    | Cons :: x:a -> List {xs:a | lessEq x xs} -> List a
@-}

insertAhead :: Foo -> List Foo -> List Foo
insertAhead new = \case
    Nil                    -> Cons new Nil
    Cons cur rest
        | new `lessEq` cur -> Cons new $ Cons cur rest
        | otherwise        -> Cons cur $ insertAhead new rest
{-@ ignore insertAhead @-}
