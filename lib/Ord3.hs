module Ord3 where

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

type Point = [Int]

-- An arbitrary ordering metric
pointLEQ :: Point -> Point -> Bool
pointLEQ [] _ = True
pointLEQ (_:_) [] = False
pointLEQ (x:xs) (y:ys) = x <= y && pointLEQ xs ys
{-@ reflect pointLEQ @-}

{-@ type LeqPoints = List<{\a b -> pointLEQ a b}> Point @-}
-- {-@ type LeqPointsLB LB = List<{\a b -> pointLEQ a b}> {

---

-- insert :: 

-- {-@ eg1 :: LeqPoints @-}
-- eg1 :: List Point
-- eg1 = Cons [0,0] (Cons [0,2] Nil)

-- {-@ eg2 :: LeqPoints @-}
-- eg2 :: List Point
-- eg2 = Cons [2,3] (Cons [2,3] Nil)

-- {-@ eg3 :: LeqPoints @-}
-- eg3 :: List Point
-- eg3 = Cons [2,3] (Cons [2,2] Nil) -- Wrong!
