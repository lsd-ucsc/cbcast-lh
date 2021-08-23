{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE KindSignatures, DataKinds #-}
{-# LANGUAGE LambdaCase, ScopedTypeVariables #-}
-- {-# LANGUAGE RankNTypes #-}
-- {-# LANGUAGE TypeFamilies #-}
module Causal.ArithmeticSemantics where

import Data.Proxy

data Peano = Z | S Peano

data Add1Rel :: Peano -> Peano -> * where
    Add1 :: Proxy p -> Add1Rel p ('S p)
    AddZ :: Add1Rel 'Z ('S 'Z) -- A redundant rule, consistent with Add1, but makes Add1Relation's semantics nondeterministic.

data Add1RelTRC :: Peano -> Peano -> * where
    Lift :: Add1Rel p1 p2 -> Add1RelTRC p1 p2
    Refl :: Add1RelTRC p p
    Tran :: Add1RelTRC a b -> Add1RelTRC b c -> Add1RelTRC a c

type Reachable p = Add1RelTRC 'Z p

z :: Proxy 'Z
z = Proxy

s :: Proxy p -> Proxy ('S p)
s Proxy = Proxy

foo :: Add1RelTRC 'Z ('S 'Z)
foo = Lift AddZ

foo' :: Add1RelTRC 'Z ('S 'Z)
foo' = Lift (Add1 z)

foo'' :: Add1RelTRC 'Z ('S 'Z)
foo'' = Tran Refl (Lift $ Add1 z)

foo''' :: Add1RelTRC 'Z ('S 'Z)
foo''' = Tran (Tran (Refl :: Add1RelTRC 'Z 'Z) (Lift $ Add1 z)) (Refl :: Add1RelTRC ('S 'Z) ('S 'Z))

class AllNatsReachable a where
    allNatsReachable :: Proxy a -> Reachable a

instance AllNatsReachable 'Z where
    allNatsReachable Proxy = Refl

instance AllNatsReachable p => AllNatsReachable ('S p) where
    allNatsReachable Proxy =
        let hyp = allNatsReachable (Proxy :: Proxy p)
            nxt = Lift $ Add1 (Proxy :: Proxy p)
        in Tran hyp nxt

-- -- `PlusEquals a b c` describes `a + b = c`
-- data PlusEquals :: Peano -> Peano -> Peano -> * where
--     PlusZ :: Peano -> PlusEquals 'Z p p
--     PlusS1 :: PlusEquals a b c -> PlusEquals ('S a) b ('S c)
--     PlusS2 :: PlusEquals a b c -> PlusEquals a ('S b) ('S c)


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
