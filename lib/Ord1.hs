module Ord1 where

data List a
    = Nil
    | Cons a (List a)
{-@
data List a <p :: a -> a -> Bool>
    = Nil
    | Cons
        { consHead :: a
        , consRest :: List a<p consHead>
        }
@-}

---

{-@ type LeqInts = List<{\x y -> x <= y}> Int @-}

---

{-@ ex1 :: LeqInts @-}
ex1 :: List Int
ex1 = Cons 2 (Cons 3 Nil)

{-@ ex2 :: LeqInts @-}
ex2 :: List Int
ex2 = Cons 2 (Cons 2 Nil)

-- {-@ ex3 :: LeqInts @-}
-- ex3 :: List Int
-- ex3 = Cons 3 (Cons 2 Nil) -- Wrong!
