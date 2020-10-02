module Bug where

{-@ inline oneFunPred @-}
oneFunPred :: Int -> Bool
oneFunPred x = x == 1

-- {-@ type OneTyAlias a = {v:a | oneFunPred v} @-}
-- 
-- {-@ data One = One { field :: OneTyAlias Int }  @-}
-- data One = One Int

{-@ data One = One { field :: {v:Int | oneFunPred v}}  @-}
data One = One Int

-- | 
-- >>> append (Cons 'a' (Cons 'b' (Cons 'c' Nil))) (Cons 'x' (Cons 'y' Nil))
-- Cons 'a' (Cons 'b' (Cons 'c' (Cons 'y' (Cons 'y' Nil))))
data List a = Cons a (List a) | Nil deriving Show
unlist :: List a -> (a -> List a -> b) -> b -> b
unlist list consHandler nilHandler = case list of
    (Cons a b) -> consHandler a b
    Nil -> nilHandler
append :: List a -> List a -> List a
append xs ys = unlist xs impl ys
  where
    impl z zs = Cons z (append zs ys)
{-@ lazy append @-}
