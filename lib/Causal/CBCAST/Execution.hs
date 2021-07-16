{-# LANGUAGE NamedFieldPuns #-}
module Causal.CBCAST.Execution where

import Redefined

---- -- Can we refine type parameters using a measure of the outer structure?
----
---- {-@ type IndexesN N = { xs:[ {n:Int | n < N} ] | len xs == N } @-}
---- {-@ type Indexes = xs:IndexesN {len xs} @-}
---- 
---- {-@ a :: Indexes @-}
---- a :: [Int]
---- a = [0, 2, 0]
---- 
---- {-@ fail b @-}
---- {-@ b :: Indexes @-}
---- b :: [Int]
---- b = [0, 3, 0]
---- 
---- {-@ fail c @-}
---- {-@ c :: Indexes @-}
---- c :: [Int]
---- c = [0, 2]

---- -- Can we define an adjacency list?
----
---- type AdjacencyList = [Set Fin]
---- {-@ type AdjacencyListN N = { xs : [Set (Fin {N})] | listLength xs == N } @-}
---- -- {-@ type AdjacencyList    = { xs : AdjacencyListN {listLength xs} | True } @-}
---- 
---- eg2 :: AdjacencyList
---- {-@ eg2 :: AdjacencyListN {0} @-}
---- eg2 = []
---- 
---- -- https://jamboard.google.com/d/1JRk9aN0vcIwFiObGgWm1A6QMzJBkd1teWfz7ThNO6kM/viewer?f=0
---- eg :: AdjacencyList
---- {-@ eg :: AdjacencyListN {6} @-}
---- eg = [ setFromList []
----     , setFromList [0]
----     , setFromList [0]
----     , setFromList [2, 1]
----     , setFromList [3]
----     , setFromList [4, 3]
----     ]

-- Can we make the adjacency list structurally recursive so that recursive functions can traverse it and return smaller parts?
--
-- N == 0       []
-- N == 1       [{}] 
-- N == 2       [{},{}]
--           or [{},{0}]
-- N == 3       [{},{},{}]
--           or [{},{},{0}]
--           or [{},{},{1}]
--           or [{},{0},{}]
--           or [{},{0},{0}]
--           or [{},{0},{1}]
--
-- Invariant:
--  * The node with index i:Nat may contain edges to k:Nat|k<i

-- Constrain dests of the current node (graphHead) to make this a DAG.
data DAGAJList = DAGAJNil | DAGAJCons DAGAJList (Set DAGAJNode)
{-@
data DAGAJList = DAGAJNil | DAGAJCons
    { graphTail :: DAGAJList
    , graphHead :: Set (DAGAJNode {graphTail})
    }
@-}

{-@ measure dagajSize @-}
dagajSize :: DAGAJList -> Int
dagajSize DAGAJNil = 0
dagajSize (DAGAJCons graphTail _) = 1 + dagajSize graphTail

type DAGAJNode = Fin
{-@ type DAGAJNode XS = Fin {dagajSize XS} @-}

n0 :: DAGAJList
n0 = DAGAJNil

n1a :: DAGAJList
n1a = DAGAJNil `DAGAJCons` setFromList []

{-@ fail n1b @-} -- Node cannot have a cycle pointing at itself.
n1b :: DAGAJList
n1b = DAGAJNil `DAGAJCons` setFromList [0]

n2a :: DAGAJList
n2a = DAGAJNil `DAGAJCons` setFromList [] `DAGAJCons` setFromList []

n2b :: DAGAJList
n2b = DAGAJNil `DAGAJCons` setFromList [] `DAGAJCons` setFromList [0]

{-@ fail n2c @-} -- Node cannot point to itself.
n2c :: DAGAJList
n2c = DAGAJNil `DAGAJCons` setFromList [0] `DAGAJCons` setFromList []

{-@ fail n2d @-} -- Node cannot point to later nodes.
n2d :: DAGAJList
n2d = DAGAJNil `DAGAJCons` setFromList [1] `DAGAJCons` setFromList []

{-@ fail n2e @-} -- Node cannot point to itself
n2e :: DAGAJList
n2e = DAGAJNil `DAGAJCons` setFromList [] `DAGAJCons` setFromList [1]

--   0
--  / \
-- 1   2
--  \ /
--   3
n4diamond :: DAGAJList
n4diamond =
    DAGAJNil
    `DAGAJCons` setFromList []
    `DAGAJCons` setFromList [0]
    `DAGAJCons` setFromList [0]
    `DAGAJCons` setFromList [1,2]

{-@ dagajNeighbors :: xs:DAGAJList -> i:DAGAJNode {xs} -> Set (Fin i) @-}
dagajNeighbors :: DAGAJList -> Int -> Set Fin
dagajNeighbors DAGAJNil _ = setEmpty
dagajNeighbors (DAGAJCons graphTail graphHead) i
    | dagajSize graphTail == i = graphHead
    | otherwise = dagajNeighbors graphTail i

{-@ dagajReachable :: xs:DAGAJList -> src:DAGAJNode {xs} -> dest:Nat -> Bool @-}
dagajReachable :: DAGAJList -> Int -> Int -> Bool
dagajReachable graph src dest = case graph of
    DAGAJNil -> False
    DAGAJCons graphTail _graphHead
        -> setMember dest srcNeighbors
        || listOrMap (\s -> dagajReachable graphTail s dest) (setAscList srcNeighbors)
  where
    srcNeighbors = dagajNeighbors graph src

--- type AdjacencyList a = [(a, Set Fin)]
--- {-@ type AdjacencyList a = gr:[(a, Set (Fin {listLength gr}))] @-}
---
--- {-@ type LL = xs:[{i:Int | i == len xs}] @-}
--- {-@ x :: LL @-}
--- x :: [Int]
--- x = [2, 2]
---
--- type Node = Fin
--- {-@ type Node G = Fin {listLength G} @-}
---
--- -- reachable :: AdjacencyList a -> Node -> Node -> Bool
--- -- {-@ reachable :: gr:AdjacencyList a -> Node {gr} -> Node {gr} -> Bool @-}
--- -- reachable gr a b = undefined
---
--- data Event pid msg
---     = Broadcast pid msg -- Process pid sends message msg to everyone.
---     | Deliver pid msg -- Process pid delivers message msg to itself.

---- type AdjacencyList = Vec (Set Fin)
---- {-@ type AdjacencyList N = Vec (SetLessN (Fin {N}) {N}) {N} @-}
----
----
---- data Graph = Graph
----     { graphSize :: Int
----     , graphAdjList :: AdjacencyList
----     }
---- {-@
---- data Graph = Graph
----     { graphSize :: Int
----     , graphAdjList :: AdjacencyList {graphSize}
----     }
---- @-}
----
---- type GraphNode = Fin
---- {-@ type GraphNode G = Fin {graphSize G} @-}
----
---- graphNodeDegree :: Graph -> GraphNode -> Fin
---- {-@ graphNodeDegree :: g:Graph -> GraphNode {g} -> Int @-}
---- -- {-@ graphNodeDegree :: g:Graph -> GraphNode {g} -> Fin {graphSize g} @-}
---- graphNodeDegree Graph{graphAdjList} node = setSize (listIndex graphAdjList node)
----
---- -- graphEdges :: Graph -> S.Set (Fin, Fin)
---- -- graphEdges [] = S.empty
---- -- graphEdges (dsts:graph) = S.empty
---- --   where
---- --     src = listLength graph
---- --     cons x xs = S.singleton x `S.union` xs
----
---- -- data Event pid msg
---- --     = Broadcast pid msg -- Process pid sends message msg to everyone.
---- --     | Deliver pid msg -- Process pid delivers message msg to itself.
---- --
---- -- data Execution pid msg = Execution
---- --     { events :: [Event pid msg]
---- --     , dependencies :: Graph
---- --     }
---- -- {-@
---- -- data Execution pid msg = Execution
---- --     { events :: [Event pid msg]
---- --     , dependencies :: Graph {listLength events}
---- --     }
---- -- @-}
---- --
---- --
---- --
---- --
---- -- executionEdges :: Execution p m -> S.Set (Event p m, Event p m)
---- -- executionEdges Execution{events, dependencies} =
---- --     case dependencies of
---- --         [] -> S.empty
----
---- -- -- TODO measures to define a valid execution
---- -- --
---- -- -- events have
---- -- deliversReferToBroadcasts :: Execution pid msg -> Bool
---- -- deliversReferToBroadcasts Execution{events, dependencies} =
----
----
---- -- gNodeDests :: Int -> Fin -> Graph -> Set Fin
---- -- {-@ gNodeDests :: n:Int -> Fin {n} -> Graph {n} -> Set (Fin {n}) @-}
---- -- gNodeDests _ n g = listIndex g n
----
---- -- -- | The graph `0 -> 1 <- 2`
---- -- _eg :: Graph
---- -- -- FIXME {-@ _eg :: Graph {3} @-}
---- -- _eg =
---- --     [ Set.singleton 1 -- 0 -> 1
---- --     , Set.empty       -- 1
---- --     , Set.singleton 1 -- 2 -> 1
---- --     ]
