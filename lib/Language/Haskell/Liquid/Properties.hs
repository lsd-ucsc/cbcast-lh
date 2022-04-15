
-- | Definitions of properties dealing with relations and binary operators.
module Language.Haskell.Liquid.Properties where

import Language.Haskell.Liquid.ProofCombinators




-- * Properties of Relations (R)

{-@ type   Reflexive a R = x:a -> {R x x} @-}
{-@ type Irreflexive a R = x:a -> {not (R x x)} @-}

{-@ type     Symmetric a R = x:a -> {y:a | R x y} -> {R y x} @-}
{-@ type    Asymmetric a R = x:a -> {y:a | R x y} -> {not (R y x)} @-}
{-@ type Antisymmetric a R = x:a -> {y:a | R x y && R y x} -> {x == y} @-}

{-@ type Transitive a R = x:a -> {y:a | R x y} -> {z:a | R y z} -> {R x z} @-}

{-@ type         Connected a R = x:a -> {y:a | x /= y} -> {R x y || R y x} @-}
{-@ type StronglyConnected a R = x:a ->  y:a           -> {R x y || R y x} @-}

-- Pre-    order              : Transitive,   Reflexive
-- Partial order (non-strict) : Transitive,   Reflexive, Antisymmetric
-- Partial order     (strict) : Transitive, Irreflexive, Antisymmetric
-- Total   order (non-strict) : Transitive,   Reflexive, Antisymmetric, Strongly Connected
-- Total   order     (strict) : Transitive, Irreflexive, Connected
-- Equivalence                : Transitive,   Reflexive, Symmetric




-- * Properties of Binary Operators (A)

{-@ type Associative a A = x:a -> y:a -> z:a -> {A (A x y) z == A x (A y z)} @-}
{-@ type Commutative a A = x:a -> y:a -> {A x y == A y x} @-}

{-@ type  MonotonicLeft t R A =        x:t -> {y:t | R x y} -> k:t -> {R (A x k) (A y k)} @-}
{-@ type MonotonicRight t R A = k:t -> x:t -> {y:t | R x y}        -> {R (A k x) (A k y)} @-}
{-@ type      Monotonic t R A = a:t -> {b:t | R a b}
                             -> x:t -> {y:t | R x y} -> {R (A a x) (A b y)} @-}




-- * Generic proofs

-- | Irreflexive and Antisymmetric imply Asymmetric.
--
--   ( ∀ x. ¬xRx )
-- ∧ ( ∀ x y. xRy ∧ yRx → x≡y )
-- ⇒
--   ( ∀ x y. xRy → ¬yRx )
{-@
irreflexiveAntisymmetric :: r:_ -> Irreflexive a {r} -> Antisymmetric a {r} -> Asymmetric a {r} @-}
irreflexiveAntisymmetric :: Eq a => (a -> a -> Bool) -> (a -> Proof) -> (a -> a -> Proof) -> (a -> a -> Proof)
irreflexiveAntisymmetric r irrefl antisym x y
    | r x y && r y x
        =   x ? antisym x y
        === y ? irrefl y
        --- `x == y && not (r y y)` contradicts the case assumption
        *** QED
    | otherwise
        = () -- case assumption is conclusion `not (r a b)` or the reverse

-- TODO: prove something like MonotonicLeft → MonotonicRight → Monotonic, etc.
