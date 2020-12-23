{-# LANGUAGE LambdaCase #-}
module Eg2 where

{-@
data Foo = Foo Int @-}
data Foo = Foo Int

lessEq :: Foo -> Foo -> Bool
lessEq (Foo a) (Foo b) = a <= b
{-@ inline lessEq @-}

data List
    = Nil
    | Cons Foo List
{-@
data List where
      Nil  ::                                       List
    | Cons :: x:Foo -> {xs:List | precedes x xs} -> List
@-}

insertAhead :: Foo -> List -> List
insertAhead new = \case
    Nil                    -> Cons new Nil
    Cons cur rest
        | new `lessEq` cur -> Cons new $ Cons cur rest
        | otherwise        -> Cons cur $ insertAhead new rest
{-@ ignore insertAhead @-}

precedes :: Foo -> List -> Bool
precedes x (Cons y _) = lessEq x y
precedes _ Nil = True
{-@ inline precedes @-}
