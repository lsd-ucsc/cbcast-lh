module DT where

import Language.Haskell.Liquid.ProofCombinators (Proof, trivial, (===), (***), QED(..))-- , (?))

import Verification (listLength)

-- WHAT ABOUT DROPWHILE IMPLEMENTED WITH BREAK?

sillyDropWhile :: (a -> Bool) -> [a] -> [a]
sillyDropWhile f xs = snd (break (not . f) xs)
-- {-@ inline sillyDropWhile @-} -- Doesn't work because snd is unbound

sillyDropWhile' :: (a -> Bool) -> [a] -> [a]
sillyDropWhile' f xs = let (_, result) = break (not . f) xs in result
-- {-@ reflect sillyDropWhile' @-} -- Doesn't work because break is unbound

-------------------------------------------------------------

app :: [a] -> [a] -> [a]
app [] bs = bs
app as [] = as
app (a:as) bs = a : app as bs
{-@ reflect app @-}

rev :: [a] -> [a]
rev [] = []
rev (a:as) = rev as `app` [a]
{-@ reflect rev @-}

{-@ assume distrP :: xs:_ -> ys:_ -> { rev (app xs ys)
                                    == app (rev xs) (rev ys) } @-}
distrP :: [a] -> [a] -> Proof
distrP _ _ = trivial

{-@ ple involP @-}
{-@
involP :: xs:_ -> {xs == rev (rev xs)} @-}
involP :: [a] -> Proof
involP []
    = rev (rev [])
    === rev []
    === []
    *** QED
involP (x:xs)
    = rev (rev (x:xs))
    === rev (rev xs `app` [x])
--      ? distrP rev x
    *** Admit

-------------------------------------------------------------

-- HOW TO PROVE TERMINATION OF FUNCTION WHOS BEHAVIOR DEPENDS ON THE RESULT OF
-- ANOTHER FUNCTION?

pop :: [a] -> ([a], Bool)
pop (_x:xs) = (xs, False)
pop [] = ([], True)
-- {-@ pop :: xs:_ -> {res :_ |      snd res  && len (fst res) == 0 || len (fst res) == len xs - 1 } @-}
-- {-@ pop :: xs:_ -> {res :_ | not (snd res) =>                       len (fst res) <  len xs     } @-}

countPops :: [a] -> Int
countPops xs =
    let (ys, isEmpty) = pop xs in
    if isEmpty then 0 else 1 + countPops
--      ys
        (const ys (pop_ResultIsSmallerProp xs))

{-@ reflect pop @-}
{-@ pop_ResultIsSmallerProp :: xs:_ ->
     { not (snd (pop xs)) =>
        len xs - 1 == len (fst (pop xs))
     } @-}
pop_ResultIsSmallerProp :: [a] -> Proof
pop_ResultIsSmallerProp [] = ()
pop_ResultIsSmallerProp (_:_) = ()

-- OK BUT DO IT AGAIN FOR A TYPE WHICH IS WRAPPED

{-@
data FooT [fooSize] @-}
data FooT a = FooC [a]

{-@
fooSize :: FooT a -> Nat @-}
fooSize :: FooT a -> Int
fooSize (FooC xs) = listLength xs
{-@ measure fooSize @-}

-- | Pop but for the FooT wrapper type
fooPop :: FooT a -> (FooT a, Bool)
fooPop (FooC xs) = (\(a, b) -> (FooC a, b)) (pop xs)

-- {-@ reflect fooPop @-}
-- {-@ fooPop_PropResultIsSmaller :: x:_ -> {
--     not (snd (fooPop x)) =>
--         fooSize x - 1 == fooSize (fst (fooPop x))
-- } @-}
-- fooPop_PropResultIsSmaller :: FooT a -> Proof
-- fooPop_PropResultIsSmaller (FooC _) = ()

-- countFooPops :: FooT a -> Int
-- countFooPops foo =
--     let (foo', isEmpty) = fooPop foo in
--     if isEmpty then 0
--     else 1 + countFooPops foo'
-- 
-- {-@ fooPop :: x:_ -> {res :_ |
--     snd res &&
--         fooSize (fst res) == 0 ||
--         fooSize (fst res) == fooSize x - 1
-- } @-}
-- 

-------------------------------------------------------------

-- HOW TO ASSERT ABOUT A CHANGE WITHIN A MAYBE WITHIN A WRAPPER TYPE?

data WrapperType a = WrapperCons {unwrap :: [a]}
{-@ measure unwrap @-}

-- | Implement some behavior which is an internal detail.
behavior :: [a] -> Maybe [a]
{-@ behavior :: x:_ -> {y:_ |
     isJust y => len x > len (fromJust y)
                         } @-}
behavior [] = Nothing
behavior (_x:xs) = Just xs

-- | Apply that behavior within some type that doesn't expose its inner '[a]'
-- clients.
encapsulation :: WrapperType a -> Maybe (WrapperType a)
{-@ encapsulation :: x:_ -> {y:_ |
     isJust y => len (unwrap x) > len (unwrap (fromJust y))
                     } @-}
encapsulation (WrapperCons xs) =
--  fmap WrapperCons (behavior xs) -- Rejected by LH, probably Functor typeclass
--  maybe Nothing (Just . WrapperCons) (behavior xs) -- Rejected by LH, but I haven't dug into why
    case behavior xs of
        Nothing -> Nothing
        Just xs' -> Just (WrapperCons xs')
