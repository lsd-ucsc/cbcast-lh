module Bar where

-- PROVE THAT A RECURSIVE FUNCTION WHICH RECURSES ON THE RESULT OF ANOTHER
-- FUNCTION DOES TERMINATE

{-@ listLen :: xs:_ -> {n:Nat | n == len xs} @-}
listLen :: [a] -> Int
listLen [] = 0
listLen (_:xs) = 1 + listLen xs
{-@ measure listLen @-}

data Bar = Bar { rawBar :: [Int]}
{-@ measure rawBar @-}

{-@ barSize :: b:_ -> {n:Nat | n == listLen (rawBar b)} @-}
barSize :: Bar -> Int
barSize (Bar xs) = listLen (rawBar (Bar xs))
{-@ measure barSize @-}

{-@ barPop :: _ -> b:_ -> {res:_ |
     (isJust res => barSize b - 1 == barSize (fst (fromJust res)))
     } @-}
barPop :: Int -> Bar -> Maybe (Bar, Int)
barPop thresh (Bar (x:xs))
    | x < thresh = Just (Bar xs, x)
    | otherwise = Nothing
barPop _ (Bar []) = Nothing

{-@ barCountPops :: _ -> b:_ -> _ / [barSize b] @-}
barCountPops :: Int -> Bar -> Int
barCountPops thresh b = case barPop thresh b of
    Just (b', _) -> 1 + barCountPops thresh b'
    Nothing -> 0

-- WHAT ABOUT IN A WRAPPER?

data Quux = Quux { rawQuux :: Bar }
{-@ measure rawQuux @-}

{-@ quuxSize :: q:_ -> {n:Nat | n == barSize (rawQuux q)} @-}
quuxSize :: Quux -> Int
quuxSize (Quux b) = barSize (rawQuux (Quux b))
{-@ measure quuxSize @-}

{-@ quuxPop :: _ -> q:_ -> {res:_ |
     (isJust res => quuxSize q - 1 == quuxSize (fst (fromJust res)))
     } @-}
quuxPop :: Int -> Quux -> Maybe (Quux, Int)
quuxPop thresh q@(Quux _) = case barPop thresh (rawQuux q) of
        Just (b, i) -> Just (Quux b, i)
        Nothing -> Nothing
