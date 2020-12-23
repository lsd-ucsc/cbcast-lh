module Ord4 where

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

data Point = PNil | PCons Int Point

-- An arbitrary ordering metric
pointLEQ :: Point -> Point -> Bool
pointLEQ PNil _ = True
pointLEQ (PCons _ _) PNil = False
pointLEQ (PCons x xs) (PCons y ys) = x <= y && pointLEQ xs ys
{-@ reflect pointLEQ @-}

{-@ type LeqPoints = List<{\a b -> pointLEQ a b}> Point @-}

--{-@ eg1 :: LeqPoints @-}
--eg1 :: List Point
--eg1 = Cons (PCons 0 (PCons 0 PNil)) (Cons (PCons 0 (PCons 2 PNil)) Nil)
