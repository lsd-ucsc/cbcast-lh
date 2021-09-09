module Data.Assoc where

import Language.Haskell.Liquid.ProofCombinators

import qualified Redefined.Bool -- Required to prevent LH elaborate makeKnowledge crash
import Redefined.Tuple
import Redefined.Proof
import Redefined.List

type Assoc k v = [(k, v)]

{-@ reflect assocEmpty @-}
assocEmpty :: Assoc k v
assocEmpty = []

{-@ reflect assocKey @-}
assocKey :: Eq k => Assoc k v -> k -> Bool
assocKey assoc key = listOrMap (firstEquals key) assoc

{-@ reflect assocValue @-}
assocValue :: Eq v => Assoc k v -> v -> Bool
assocValue assoc value = listOrMap (secondEquals value) assoc

{-@ ple assocKeyLookupIsJust @-}
{-@ assocKeyLookupIsJust :: a:Assoc k v -> {key:k | assocKey a key} -> { isJust (assocLookup a key)} @-}
assocKeyLookupIsJust :: Eq k => Assoc k v -> k -> Proof
assocKeyLookupIsJust (kv:kvs) key = case assocLookup (kv:kvs) key of
    Just _ -> () *** QED
    Nothing -> () *** Admit -- TODO

-- | Look for a value associated with the key.
{-@ reflect assocLookup @-}
assocLookup :: Eq k => Assoc k v -> k -> Maybe v
assocLookup assoc key = listFoldr (assocLookupHelper key) Nothing assoc
-- | Once a match is found, put it in the accumulator and then keep it there.
{-@ reflect assocLookupHelper @-}
assocLookupHelper :: Eq k => k -> (k, v) -> Maybe v -> Maybe v
assocLookupHelper key (k, v) Nothing = if key == k then Just v else Nothing
assocLookupHelper _key _item found@Just{} = found

{-@ reflect assocKeyLookup @-}
{-@ assocKeyLookup :: a:Assoc k v -> {key:k | assocKey a key} -> v @-}
assocKeyLookup :: Eq k => Assoc k v -> k -> v
assocKeyLookup assoc key =
    case assocLookup assoc key `proofConst` assocKeyLookupIsJust assoc key of
        Just v -> v

-- | Call the function to update the value associated with the key, or insert a new one.
{-@ reflect assocUpdate @-}
assocUpdate :: Eq k => Assoc k v -> k -> (Maybe v -> v) -> Assoc k v
assocUpdate [] key f = (key, f Nothing):[]
assocUpdate ((k,v):rest) key f
    | k == key = (k,f (Just v)):rest
    | otherwise = (k,v):assocUpdate rest key f

-- | Cons one value onto the list associated with the key, or insert a singleton list.
{-@ reflect assocCons @-}
assocCons :: Eq k => Assoc k [a] -> k -> a -> Assoc k [a]
assocCons assoc key x = assocUpdate assoc key (assocConsHelper x)
-- | Cons to the list, or make a list of one.
{-@ reflect assocConsHelper @-}
assocConsHelper :: a -> Maybe [a] -> [a]
assocConsHelper x (Just xs) = x:xs
assocConsHelper x Nothing = x:[]
