{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE LambdaCase #-}
module Causal.Scratch where

-- | This is the easiest "insertOrCombine" impl that just uses a polymorphic
-- datatype which expresses the ordering constraint straightforwardly on the
-- keys

data AssocDT k v
    = ANil
    | ACons k v (AssocDT k v)
{-@
data AssocDT k v where
      ANil  :: AssocDT k v
    | ACons :: key:k -> val:v -> AssocDT {keys:k | key < keys} _ -> AssocDT k v
@-}

insertOrCombine :: (Ord k) => (v -> v -> v) -> k -> v -> AssocDT k v -> AssocDT k v
insertOrCombine combine newK newV assoc = case assoc of
    ANil               -> ACons newK newV ANil
    ACons curK curV rest
        | newK <  curK -> ACons newK newV $ ACons curK curV rest
        | newK == curK -> ACons curK (newV`combine`curV) rest
        | otherwise    -> ACons curK curV $ insertOrCombine combine newK newV rest
{-@ reflect insertOrCombine @-}



-- | This is the next-harder "insertOrCombine" impl which is monomorphic and
-- therefore must express its ordering constraint differently .. it's also
-- ordered on a field of the element type, which makes this more similar to the
-- delay-queue

{-@
data Thing = Thing {tKey::Int,tVal::Float} @-}
data Thing = Thing {tKey::Int,tVal::Float}

{-@
tMerge :: a:_ -> {b:_ | tKey a == tKey b} -> {c:_ | tKey b == tKey c} @-}
tMerge :: Thing -> Thing -> Thing
tMerge a b = a{tVal = tVal a + tVal b}
{-@ inline tMerge @-}

data Things
    = TNil
    | TCons Thing Things
{-@
data Things where
      TNil :: Things
    | TCons ::   x:Thing -> {xs:Things | tPrecedes x xs} -> Things
@-}

tPrecedes :: Thing -> Things -> Bool
tPrecedes _  TNil       = True
tPrecedes a (TCons b _) = tKey a < tKey b
{-@ inline tPrecedes @-}

-- tInsertBefore :: Thing -> Things -> Things
-- tInsertBefore new = \case
--     TNil                                  -> TCons  new               TNil
--     TCons cur rest | tKey new <  tKey cur -> TCons  new             $ TCons cur rest
--                    | tKey new == tKey cur -> TCons (tMerge new cur) $ rest
--                    | otherwise            -> tInsertBefore cur $ tInsertBefore new rest
-- {-@ reflect tInsertBefore @-}



-- | This is yet closer to the delay-queue in that it is a monomorphic type
-- ordered with LEQ on a field of the element type

{-@
data Zap = Zap {zKey::Int,zVal::Float} @-}
data Zap = Zap {zKey::Int,zVal::Float}

data Zaps
    = ZNil
    | ZCons Zap Zaps
{-@
data Zaps [zSize] where
      ZNil :: Zaps
    | ZCons ::   x:Zap -> {xs:Zaps | zPrecedes x xs} -> Zaps
@-}

{-@
zSize :: _ -> Nat @-}
zSize :: Zaps -> Int
zSize  ZNil = 0
zSize (ZCons _ rest) = 1 + zSize rest
{-@ measure zSize @-}

zPrecedes :: Zap -> Zaps -> Bool
zPrecedes _  ZNil       = True
zPrecedes a (ZCons b _) = zKey a <= zKey b
{-@ inline zPrecedes @-}

{-@
zInsertAhead :: x:Zap -> Zaps -> {xs:Zaps | zPrecedes x xs} @-}
zInsertAhead ::   Zap -> Zaps ->     Zaps
zInsertAhead new = \case
    ZNil                                  -> ZCons new ZNil
    ZCons cur rest | zKey new <= zKey cur -> ZCons new $ ZCons cur rest
--                 | otherwise            -> ZCons cur $ zInsertAhead new rest
                   | otherwise            -> zInsertAhead new rest -- wrong

--zInsertBeyond :: Zap -> Zaps -> Zaps
--zInsertBeyond new = \case
--    ZNil                       -> ZCons new ZNil
--    ZCons cur rest
--        | zKey cur <= zKey new -> ZCons cur $ zInsertBeyond new rest
----      | otherwise            -> zInsertBeyond y $ zInsertBeyond x ys
--        | otherwise            -> rest -- wrong
--{-@ reflect zInsertBeyond @-}

---- {-@
---- zUncons :: Zaps -> Maybe (Zap, Zaps)<{\x xs -> zPrecedes x xs}> @-}
---- zUncons :: Zaps -> Maybe (Zap, Zaps)
---- zUncons ZNil = Nothing
---- zUncons (ZCons x xs) = Just (x, xs)
---- 
---- zInsertAhead :: Zap -> Zaps -> Zaps
---- zInsertAhead new zaps = case zUncons zaps of
----     Nothing                               -> ZCons new ZNil
----     Just (cur,rest)| zKey new <= zKey cur -> ZCons new $ ZCons cur rest
---- --                 | otherwise            -> ZCons cur $ zInsertAhead new rest
----                    | otherwise            -> zInsertAhead new rest -- wrong




{-@
data Quux k = Quux {qKey::k,qVal::Float} @-}
data Quux k = Quux {qKey::k,qVal::Float}

data Quuxes k
    = QNil
    | QCons (Quux k) (Quuxes k)
{-@
data Quuxes k <p :: k -> k -> Bool>
    = QNil
    | QCons
        { hd :: Quux k
        , tl :: Quuxes<p> (k<p hd>)
        }
@-}

--qUncons :: Quuxes k -> Maybe (Quux k, Quuxes k)
--qUncons QNil = Nothing
--qUncons (QCons x xs) = Just (x, xs)
--
--eg :: Quuxes k -> Quuxes k
--eg qs = case qUncons qs of
--    Nothing -> qs
--    Just (x, xs) -> QCons x xs

-- {-@
-- qInsertAhead :: leq:(Quux k -> Quux k -> Bool) -> Quux k -> Quuxes<{\a b -> leq a b}> k -> Quuxes k @-}
-- qInsertAhead ::     (Quux k -> Quux k -> Bool) -> Quux k -> Quuxes                    k -> Quuxes k
-- qInsertAhead leq new = \case
--     QNil                           -> QCons new QNil
--     QCons cur rest | new `leq` cur -> QCons new $ QCons cur rest
--                    | otherwise     -> QCons cur $ qInsertAhead leq new rest
-- 



-- type Item k v = (k,v)
-- type ListAssoc k v = [Item k v]
-- {-@ type SortAssoc k v = [Item k v]<{\a b -> fst a < fst b}> @-}
-- 
-- {-@
-- ins ::            (v -> v -> v) -> Item k v -> assoc:(SortAssoc k v) -> SortAssoc k v / [len assoc] @-}
-- ins :: (Ord k) => (v -> v -> v) -> Item k v -> ListAssoc k v -> ListAssoc k v
-- ins combine new@(newK,newV) = \case
--     [] -> [new]
--     cur@(curK,curV):rest
--         | newK <  curK -> new:cur:rest
--         | newK == curK -> (curK,newV`combine`curV):rest
--         | otherwise -> ins combine cur $ ins combine new rest

type Item k v = (k,v)
type Assoc k v = [Item k v]
{-@ type SortedAssoc k v = [Item k v]<{\a b -> fst a <= fst b}> @-}
{-@ type SortedAssocLB k v LB = SortedAssoc {key:k | LB <= key} v @-}

{-@ egSA :: SortedAssoc Int String @-}
egSA :: Assoc Int String
egSA = [(3,"foo"), (5,"bar")]

-- {-@ egConv :: SortedAssocLB Int String 3 @-}
-- egConv :: Assoc Int String
-- egConv = egSA

{-@
aFirstKeyOr :: SortedAssoc k v -> k -> k @-}
aFirstKeyOr :: Assoc k v -> k -> k
aFirstKeyOr assoc def = case assoc of
    (k,_):_ -> k
    [] -> def
{-@ inline aFirstKeyOr @-}

-- {-@
-- aHead :: {xs:SortedAssoc k v | xs /= []} -> k @-}
-- aHead :: Assoc k v -> k
-- aHead = \case
--     (k,_):_ -> k
-- {-@ inline aHead @-}



-- 
-- {-@
-- aBoundedBy :: lb:k -> SortedAssoc {key:k | lb <= key} v -> SortedAssocLB k v lb @-}
-- aBoundedBy :: k -> Assoc k v -> Assoc k v
-- aBoundedBy _ xs = xs
-- {-@ inline aBoundedBy @-}

--{-@
--foo :: SortedAssocLB Int String 2 @-}
--foo :: Assoc Int String
--foo = aBoundedBy 3 []

-- aIsBound :: k -> Assoc k v -> Bool
-- aIsBound lb = \case
--     (k,_):_ -> k
--     [] -> True

-- 
-- {-@
-- aBounded :: xs:SortedAssoc k v -> lb:k -> SortedAssocLB k v (aFirstKeyOr xs lb) @-}
-- aBounded ::          Assoc k v ->    k ->       Assoc   k v
-- aBounded xs _ = xs

---- -- {-@
---- -- uncons :: SortedAssoc k v -> Maybe (t:Item k v, SortedAssocLB k v (fst t)) @-}
---- -- uncons :: Assoc k v -> Maybe (Item k v, Assoc k v)
---- -- uncons [] = Nothing
---- -- uncons (x:xs) = Just (x,xs)
----
---- -- DESTRUCTURING WITH THIS FUNCTION SHOULD BE SUFFICIENT TO WRITE insertOrCombine WITH CONS
----
----
---- ---- {-@
---- ---- data KV a b = KV {kvKey::a, kvVal::b} @-}
---- ---- data KV a b = KV {kvKey::a, kvVal::b}
---- ----
---- ---- {-@
---- ---- type OKVs k v = [KV k v]<{\a b -> kvKey a < kvKey b}> @-}
---- ---- type  KVs k v = [KV k v]
---- ----
---- ---- {-@
---- ---- ins ::                         KV k v -> OKVs k v -> OKVs k v @-}
---- ---- ins :: (Ord k, Semigroup v) => KV k v ->  KVs k v ->  KVs k v
---- ---- ins new@(KV newK newV) assoc = case assoc of
---- ----     []                          -> [new]
---- ----     cur@(KV curK curV) : rest
---- ----         | newK <  curK          -> new                   : cur : rest
---- ----         | newK == curK          -> cur{kvVal=newV<>curV} : rest
---- ----         | otherwise             -> cur                   : ins new rest
