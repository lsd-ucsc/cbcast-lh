module DT where

-- HOW TO PROVE TERMINATION OF fooLen, WHOS BEHAVIOR DEPENDS ON THE
-- RESULT OF ANOTHER FUNCTION?

data FooT a = FooC {unfoo::[a]}
{-@ measure unfoo @-}

-- | Unconditionally remove first element and return a bool
-- indicating whether the input (and therefore output) is empty.
{-@
fooPop
    :: x:_
    -> { y:_ |
        0 == len x &&
            (len x == len (fst y) &&      snd y ) ||
            (len x >  len (fst y) && not (snd y))
    }
@-}
fooPop :: [a] -> ([a], Bool)
fooPop [] = ([], True)
fooPop (_x:xs) = (xs, False)

{-@
fooLen :: x:FooT a -> Nat / [len (unfoo x)] @-}
fooLen :: FooT a -> Int
fooLen b =
    let (rest, isEmpty) = fooPop (unfoo b)
    in
    if isEmpty
    then 0
    else 1 + fooLen b{unfoo=rest}
--  else 1 + fooLen (FooC rest)

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
