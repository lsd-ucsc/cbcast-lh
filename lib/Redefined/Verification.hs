
-- | Proofs about the redefined stdlib items.
module Redefined.Verification {-# WARNING "Verification only" #-} where

import Language.Haskell.Liquid.ProofCombinators

import Redefined

-- * proofs about lists

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

-- * proofs about foldr and helpers

{-@
listFoldrEmpty
    ::     f : (a -> b -> b)
    -> first : b
    -> { first == listFoldr f first [] }
@-}
listFoldrEmpty :: (a -> b -> b) -> b -> Proof
listFoldrEmpty _f _first = () {-@ ple listFoldrEmpty @-}

{-@
listFoldrPenultimate
    ::        f : (a -> b -> b)
    ->        v :  a
    ->       vs : [a]
    ->    first :  b
    -> { penult :  b  | penult == listFoldr f first         vs  }
    -> {   last :  b  |   last == listFoldr f first (cons v vs) }
    -> { f v penult == last }
@-}
listFoldrPenultimate :: (a -> b -> b) -> a -> [a] -> b -> b -> b -> Proof
listFoldrPenultimate _f _v _vs _first _penult _last = () {-@ ple listFoldrPenultimate @-}

{-@ funFlip'Apply :: f:(a -> b -> c) -> b:b -> a:a -> { funFlip' f b a == f a b } @-}
funFlip'Apply :: (a -> b -> c) -> b -> a -> Proof
funFlip'Apply _ _ _ = () {-@ ple funFlip'Apply @-}

{-@ funUncurry'Apply :: f:(a -> b -> c) -> v:(a, b) -> { funUncurry' f v == f (fst v) (snd v) } @-}
funUncurry'Apply :: (a -> b -> c) -> (a, b) -> Proof
funUncurry'Apply _ (_,_) = () {-@ ple funUncurry'Apply @-}

-- * proofs about lists of unique elements

{-@
uniqueListHeadNotInTail' :: {xs:[a]<{\j k -> j /= k}> | xs /= []} -> {not (listElem (head xs) (tail xs))} @-}
uniqueListHeadNotInTail' :: Eq a => [a] -> Proof
uniqueListHeadNotInTail' (x:xs) = uniqueListHeadNotInTail x xs

-- | The head is not in the tail of a list containing unique elements. This
-- type looks weird, but the relationship between e and xs is exactly what a
-- unique list expresses (see (uniqueListHeadNotInTail'@). The purpose of
-- keeping this lemma around is it allows callers to call with arguments that
-- don't prove the list is nonempty.
{-@
uniqueListHeadNotInTail
    :: e:a -> xs:[{x:a | e /= x}] -> {not (listElem e xs)} @-}
uniqueListHeadNotInTail :: Eq a => a -> [a] -> Proof
uniqueListHeadNotInTail e [] = listElem e [] *** QED
uniqueListHeadNotInTail e (x:xs) =
        listElem e (x:xs)
    === (e==x || listElem e xs)
    === listElem e xs
        ? uniqueListHeadNotInTail e xs
    *** QED
