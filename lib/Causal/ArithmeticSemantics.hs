{-# LANGUAGE GADTs #-}
-- {-# LANGUAGE TypeOperators #-}
{-# LANGUAGE KindSignatures, DataKinds #-}
{-# LANGUAGE RankNTypes #-}
-- {-# LANGUAGE TypeFamilies #-}
module Causal.ArithmeticSemantics where

{-@ data Peano = Z | S { unS :: Peano } @-}
data Peano = Z | S { unS :: Peano }

---- -- data a :==> b where
---- --     (:+) :: a -> b -> a :==> b
---- 

data Add1Relation :: Peano -> Peano -> * where
    Add1 :: forall p. Add1Relation p ('S p)
    AddZ :: Add1Relation 'Z ('S 'Z) -- A redundant rule, consistent with Add1, but makes Add1Relation's semantics nondeterministic.

data Add1RelTRC :: Peano -> Peano -> * where
    Lift :: forall p1 p2. Add1Relation p1 p2 -> Add1RelTRC p1 p2
    Refl :: forall p. Add1RelTRC p p
    Tran :: forall a b c. Add1RelTRC a b -> Add1RelTRC b c -> Add1RelTRC a c

type Reachable (p :: Peano) = Add1RelTRC 'Z p

foo :: Add1RelTRC 'Z ('S 'Z)
foo = Lift AddZ

foo' :: Add1RelTRC 'Z ('S 'Z)
foo' = Lift Add1

foo'' :: Add1RelTRC 'Z ('S 'Z)
foo'' = Tran Refl (Lift Add1)

foo''' :: Add1RelTRC 'Z ('S 'Z)
foo''' = Tran (Tran (Refl :: Add1RelTRC 'Z 'Z) (Lift Add1)) (Refl :: Add1RelTRC ('S 'Z) ('S 'Z))

allNatsReachable :: forall (p :: Peano). Reachable p
allNatsReachable = undefined -- Gan says: Case split on p (but we can't do that, because it's a type)


data PlusEquals :: Peano -> Peano -> Peano -> * where
    PlusZ :: forall p. PlusEquals 'Z p p
    PlusS1 :: forall a b c. PlusEquals a b c -> PlusEquals ('S a) b ('S c)
    PlusS2 :: forall a b c. PlusEquals a b c -> PlusEquals a ('S b) ('S c)


---- -- data family PE2 :: Peano -> Peano -> Peano -> *
---- -- data instance PE2 (p :: Peano) = 
---- --  PZ (p :: Peano) -> 
---- 
---- foo :: PE 'Z ('S 'Z) ('S 'Z)
---- foo = PZ

--- data PlusEquals where
---     PlusZ :: Peano -> Peano -> Peano -> PlusEquals
---     PlusS :: Peano -> Peano -> Peano -> PlusEquals
--- {-@
--- data PlusEquals where
---     PlusZ
---         :: { z:Peano | z == Z}
---         ->   p:Peano
---         -> {p':Peano | p == p'}
---         -> PlusEquals
---     PlusS
---         ::   sp':Peano
---         ->     p:Peano
---         ->  sp'':Peano
---         -> {pe:PlusEquals | pe == PlusS (unS sp') p (unS sp'') }
--- @-}

-- data PlusEquals (a::Peano) (b::Peano) (c::Peano) where
--     PZ :: (z::Peano) -> (p::Peano) -> (p::Peano) -> PlusEquals a b c
