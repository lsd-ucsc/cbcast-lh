
-- | Proofs about the redefined stdlib items.
module Redefined.Verification where

import Language.Haskell.Liquid.ProofCombinators

import Redefined

-- | If e is in x:xs but e isn't x then e is in xs.
--
-- ∀e,x,xs. e∈x:xs ∧ e≠x ⇒ e∈xs
{-@ tailElem :: e:_ -> {x:_ | e /= x} -> {yzs:_ | listElem e (cons x yzs)} -> { listElem e yzs } @-}
tailElem :: Eq a => a -> a -> [a] -> Proof
tailElem e x []             =   impossible
    {-restate premise-}     $   listElem e (x:[])
    {-by def of listElem-}  === (e==x || listElem e [])
    {-by e/=x premise-}     === listElem e []
    {-premise failed-}      *** QED
tailElem e x (y:zs)
    {-restate premise-}     =   listElem e (x:y:zs)
    {-by def of listElem-}  === (e==x || listElem e (y:zs))
    {-by e/=x premise-}     === listElem e (y:zs)
                            *** QED

-- | If e is in xs then e is in w:xs.
--
-- ∀e,xs,w. e∈xs ⇒ e∈w:xs.
{-@
extendElem
    :: e:_
    -> {xs:_ | listElem e xs}
    -> w:_
    -> {listElem e (cons w xs)}
@-}
extendElem :: Eq a => a -> [a] -> a -> Proof
extendElem e [] _w      =   impossible
    {-restate premise-} $   listElem e []
extendElem e xs w
    {-restate conclusion-}  =   listElem e (w:xs)
    {-by def of listElem-}  === (e==w || listElem e xs)
    {-restate premise-}     === listElem e xs
                            *** QED

-- | If e is in the tail following h within xxs, then e is in xxs. Being in a
-- sublist implies membership in the list containing that sublist.
--
-- ∀e,h,xxs. e∈…:h:xxs ⇒ e∈xxs
{-@
truncateElemTail4Head
    :: e:_
    -> h:_
    -> {xxs:_ | listElem e (listTailForHead h xxs) }
    -> { listElem e xxs }
@-}
truncateElemTail4Head :: Eq a => a -> a -> [a] -> Proof
truncateElemTail4Head e h []        =   impossible
    {-restate premise-}             $   listElem e (listTailForHead h [])
    {-by def of listTailForHead-}   === listElem e []
truncateElemTail4Head e h (x:xs)
    | h == x
        {-restate premise-}             =   listElem e (listTailForHead h (x:xs))
        {-by def of listTailForHead-}   === listElem e (if h==x then xs else listTailForHead h xs)
        {-simplify IfThenElse-}         === listElem e xs
        ? extendElem e xs x             === listElem e (x:xs)
                                        *** QED
    | otherwise
        {-restate premise-}             =   listElem e (listTailForHead h (x:xs))
        {-by def of listTailForHead-}   === listElem e (if h==x then xs else listTailForHead h xs)
        {-simplify IfThenElse-}         === listElem e (listTailForHead h xs)
        ? truncateElemTail4Head e h xs  === listElem e xs
        ? extendElem e xs x             === listElem e (x:xs)
                                        *** QED

-- | If e is in the tail following h within xs, then e is also in the tail
-- following h within w:xs. Consing a new element to a list doesn't change
-- relationships among things inside that list.
--
-- ∀e,h,xxs. e∈…:h:xxs ⇒ e∈w:…:h:xxs
{-@
extendElemTail4Head
    :: e:_
    -> h:_
    -> {xs:_ | listElem e (listTailForHead h xs) }
    -> w:_
    -> { listElem e (listTailForHead h (cons w xs)) }
@-}
extendElemTail4Head :: Eq a => a -> a -> [a] -> a -> Proof
extendElemTail4Head e h [] _w       =   impossible
    {-restate premise-}             $   listElem e (listTailForHead h [])
    {-by def of listTailForHead-}   === listElem e []
extendElemTail4Head e h xs w -- by cases of listTailForHead
    | h == w
        {-restate conclusion-}          =   listElem e (listTailForHead h (w:xs))
        {-by def of listTailForHead-}   === listElem e (if h==w then xs else listTailForHead h xs)
        {-simplify IfThenElse-}         === listElem e xs
        ? truncateElemTail4Head e h xs  *** QED
    | otherwise
        {-restate conclusion-}          =   listElem e (listTailForHead h (w:xs))
        {-by def of listTailForhead-}   === listElem e (if h==w then xs else listTailForHead h xs)
        {-simplify IfThenElse-}         === listElem e (listTailForHead h xs)
                                        *** QED
