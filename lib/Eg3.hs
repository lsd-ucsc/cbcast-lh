{-# LANGUAGE LambdaCase #-}
module Eg3 where

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
data List a <p :: a -> a -> Bool> where
      Nil  ::                          List<p> a
    | Cons :: x:a -> List<p> a<p x> -> List<p> a
@-}

{-@ type Foos = List<{\a b -> lessEq a b}> Foo @-}

{-@ insertAhead :: Foo -> Foos -> Foos @-}
insertAhead :: Foo -> List Foo -> List Foo
insertAhead new = \case
    Nil                    -> Cons new Nil
    Cons cur rest
        | new `lessEq` cur -> Cons new $ Cons cur rest
        | otherwise        -> Cons cur $ insertAhead new rest
