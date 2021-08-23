{-# LANGUAGE GADTs #-}
module Causal.ArithmeticSemanticsHybrid where

data Peano = Z | S Peano deriving Eq

{-@ reflect add1Rel @-}
add1Rel :: Peano -> Peano -> Bool
-- AddZ rule
add1Rel Z (S Z) = True
-- Add1 rule
add1Rel p (S p') = p == p'
-- Otherwise ..
add1Rel _ _ = False

---- type Add1Rel = Add1Rel Peano Peano
---- {-@
---- data Add1Rel = Add1Rel
----     { lt  :: Peano
----     , rt' :: { rt : Peano | add1Rel lt rt }
----     }
---- @-}
type Add1Rel = (Peano, Peano)
{-@ type Add1Rel = (Peano, Peano)<{\a b -> add1Rel a b}> @-}

-- type State = Peano
-- 
-- data Add1Rel where
--     Add1 :: State -> State -> Add1Rel State
-- --  AddZ :: Add1Rel 'Z ('S 'Z) -- A redundant rule, consistent with Add1, but makes Add1Relation's semantics nondeterministic.
