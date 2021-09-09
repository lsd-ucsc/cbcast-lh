{-# LANGUAGE NamedFieldPuns #-}
module Data.DAG where

import Redefined.Fin
import Redefined.List
import Redefined.Set

-- * Graph

-- | Define directed acyclic graph in adjacency list representation suitable
-- for structurally recursive traversal which maintains appropriate size and
-- indexing relationships.
--
-- N == 0
--          []
--
-- N == 1
--           0
--          [{}]
--
-- N == 2
--           0  1
--          [{},{}]
--       or [{},{0}]
--
-- N == 3
--           0  1  2
--          [{},{},{}]
--       or [{},{},{0}]
--       or [{},{},{1}]
--       or [{},{0},{}]
--       or [{},{0},{0}]
--       or [{},{0},{1}]
--
-- Invariant:
--  * The node with index i:Nat may contain edges to k:Nat|k<i

-- Constrain neighbors of the current node (gHead) to those in the rest of the
-- graph (gTail).
data DAG = DAGnil | DAGcons DAG (Set DAGnode)
{-@
data DAG = DAGnil | DAGcons
    { gTail :: DAG
    , gHead :: Set (DAGnode {gTail})
    }
@-}

{-@ measure gSize @-}
gSize :: DAG -> Int
gSize DAGnil = 0
gSize (DAGcons gTail _gHead) = 1 + gSize gTail

type DAGnode = Fin
{-@ type DAGnode XS = Fin {gSize XS} @-}

n0 :: DAG
n0 = DAGnil

n1a :: DAG
n1a = DAGnil `DAGcons` setFromList []

{-@ fail n1b @-} -- Node cannot have a cycle pointing at itself.
n1b :: DAG
n1b = DAGnil `DAGcons` setFromList [0]

n2a :: DAG
n2a = DAGnil `DAGcons` setFromList [] `DAGcons` setFromList []

n2b :: DAG
n2b = DAGnil `DAGcons` setFromList [] `DAGcons` setFromList [0]

{-@ fail n2c @-} -- Node cannot point to itself.
n2c :: DAG
n2c = DAGnil `DAGcons` setFromList [0] `DAGcons` setFromList []

{-@ fail n2d @-} -- Node cannot point to later nodes.
n2d :: DAG
n2d = DAGnil `DAGcons` setFromList [1] `DAGcons` setFromList []

{-@ fail n2e @-} -- Node cannot point to itself
n2e :: DAG
n2e = DAGnil `DAGcons` setFromList [] `DAGcons` setFromList [1]

--   0
--  / \
-- 1   2
--  \ /
--   3
n4diamond :: DAG
n4diamond = DAGnil
    `DAGcons` setFromList []    -- 0
    `DAGcons` setFromList [0]   -- 1
    `DAGcons` setFromList [0]   -- 2
    `DAGcons` setFromList [1,2] -- 3

-- 0  1
-- |\ |
-- | \|
-- 2  3
n4enn :: DAG
n4enn = DAGnil
    `DAGcons` setFromList []    -- 0
    `DAGcons` setFromList []    -- 1
    `DAGcons` setFromList [0]   -- 2
    `DAGcons` setFromList [0,1] -- 3

-- | Index into the DAG adjacency list and return the neighbor set of the i-th
-- node away from nil.
{-@ gNeighbors :: xs:DAG -> i:DAGnode {xs} -> Set (Fin i) @-}
gNeighbors :: DAG -> Int -> Set Fin
gNeighbors (DAGcons gTail gHead) i
    | gSize gTail == i = gHead
    | otherwise = gNeighbors gTail i

-- | Is dest in the neighbor-set of src, or transitively in any of their
-- neighbor sets?
--
-- >>> listMap (gReachable n4diamond 0) [0, 1, 2, 3]
-- [False,False,False,False]
-- >>> listMap (gReachable n4diamond 1) [0, 1, 2, 3]
-- [True,False,False,False]
-- >>> listMap (gReachable n4diamond 2) [0, 1, 2, 3]
-- [True,False,False,False]
-- >>> listMap (gReachable n4diamond 3) [0, 1, 2, 3]
-- [True,True,True,False]
--
-- >>> listMap (gReachable n4enn 0) [0, 1, 2, 3]
-- [False,False,False,False]
-- >>> listMap (gReachable n4enn 1) [0, 1, 2, 3]
-- [False,False,False,False]
-- >>> listMap (gReachable n4enn 2) [0, 1, 2, 3]
-- [True,False,False,False]
-- >>> listMap (gReachable n4enn 3) [0, 1, 2, 3]
-- [True,True,False,False]
--
{-@ gReachable :: xs:DAG -> src:DAGnode {xs} -> dest:Nat -> Bool @-}
gReachable :: DAG -> Int -> Int -> Bool
gReachable graph src dest = case graph of
    DAGcons gTail _graphHead
        -> setMember dest srcNeighbors
        || listOrMap (\s -> gReachable gTail s dest) (setAscList srcNeighbors)
  where
    srcNeighbors = gNeighbors graph src
