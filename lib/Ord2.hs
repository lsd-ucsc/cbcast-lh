module Ord2 where

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

type Point = (Int, Int)

-- An arbitrary ordering metric
pointLEQ :: Point -> Point -> Bool
pointLEQ (a1, a2) (b1, b2) = a1 <= b1 && a2 <= b2
{-@ inline pointLEQ @-}
pointLEQpoints :: Point -> List Point -> Bool
pointLEQpoints _ Nil = True
pointLEQpoints x (Cons y _) = pointLEQ x y
{-@ inline pointLEQpoints @-}

---

{-@ type LeqPoints = List<{\a b -> pointLEQ a b}> Point @-}

-- {-@ type LeqPointsLB LB = List<{\a b -> pointLEQ a b}> {pt:Point | pointLEQ LB pt} @-}
--
-- {-@
-- uncons :: List Point -> Maybe (Point, List Point)<{\x xs -> pointLEQpoints x xs}> @-}
-- uncons :: List Point -> Maybe (Point, List Point)
-- uncons Nil = Nothing
-- uncons (Cons x xs) = Just (x, xs)

---

{-@ eg1 :: LeqPoints @-}
eg1 :: List Point
eg1 = Cons (0,0) (Cons (0,2) Nil)

{-@ eg2 :: LeqPoints @-}
eg2 :: List Point
eg2 = Cons (2,3) (Cons (2,3) Nil)

-- {-@ eg3 :: LeqPoints @-}
-- eg3 :: List Point
-- eg3 = Cons (2,3) (Cons (2,2) Nil) -- Wrong!

---
