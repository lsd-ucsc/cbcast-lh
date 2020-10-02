{-# LANGUAGE QuasiQuotes #-}
module Confusions where

import LiquidHaskell (lq)
import Data.Int

--------------------------------------------------
-- Actually it turns out I still don't understand the meaning of these
-- things??:
--      inline
--          Copy the definition of the function to the SMT logic?
--      measure
--          Copy the refinements in the type to the constructors of the data
--          type?
--      reflect
--          Make an uninterpreted function and copy the definition of the
--          function into the SMT logic in a predicate which is in the
--          refinement type for the uninterpreted function.

--------------------------------------------------
-- (9) a data structure doesn't have refinements that allow it to behave like a
-- data structure, unless you do some incantations that imply that LH should
-- add them
--
-- Containers.hs

--------------------------------------------------
-- (8) lots of arbitrary requirements for use of an extrinsic property
-- https://liquidhaskell.slack.com/archives/C54QAL9RR/p1601419325043700?thread_ts=1601416686.041700&cid=C54QAL9RR

--------------------------------------------------
-- (7) trivial recursive function which confuses the measure

-- | Measure for a list
myLen :: [a] -> Int
myLen ([]) = 0
myLen ((_x:xs)) = 1 + myLen (xs)
{-@ measure myLen @-}

-- | Data structure hiding a list internally
data Foo a = Foo [a] deriving Show

-- | Measure for Foo which delegates to the measure for a list
fooLen :: Foo a -> Int
fooLen (Foo xs) = myLen xs
{-@ measure fooLen @-}

-- | Specification for Foo which assigns the measure to it
{-@ data Foo [fooLen] @-}

fooLen2 :: Foo a -> Int
fooLen2 (Foo []) = 0
fooLen2 (Foo (_x:xs)) = 1 + fooLen2 (Foo xs)
-- Why is fooLen2 rejected?
-- https://liquidhaskell.slack.com/archives/C54QAL9RR/p1600905279008400
-- resulted in GH issue https://github.com/ucsd-progsys/liquidhaskell/issues/1766

-- Solution:
{-@ myLen :: _ -> {x:_ | 0 <= x} @-}

-- Why: termination checker not only constrains the size of recursive component
-- to be smaller, but also on minimum size of recursive component.

--------------------------------------------------

-- (6) bugs around scoping
-- importing measures defined by quasiquoter https://github.com/ucsd-progsys/liquidhaskell/issues/1764
-- using an alias which uses an inlined function https://github.com/ucsd-progsys/liquidhaskell/issues/1761

-- (5)
-- Wrong number of fields error on
-- {-@
-- data Pt = Pt Int Int @-}
-- data Pt = Pt Int Int
-- ?? a bug but fixed already

-- (4)
-- How do you define a measure for data based on the size of a list?
-- EG. using the length defined in prelude which comes from data.foldable?
-- https://liquidhaskell.slack.com/archives/C54QAL9RR/p1600669515051900

-- (3)
-- some confusion about how to abstract a refinement
-- https://liquidhaskell.slack.com/archives/C54QAL9RR/p1600451110042700
-- three different approaches
-- there was also a bug

-- (2)
-- don't use newtype with refined data types; it's not really supported
-- * the refinement type will treat the newtype like there's no wrapper
-- * ranjit said the stripped constructor is a problem

-- (1)
-- found three bugs:
-- https://liquidhaskell.slack.com/archives/C54QAL9RR/p1600412369018800?thread_ts=1600404760.006900&cid=C54QAL9RR
-- * https://github.com/ucsd-progsys/liquidhaskell/issues/1758 (only linked here)
-- * https://github.com/ucsd-progsys/liquidhaskell/issues/1757 (also linked mid-thread)
-- * https://github.com/ucsd-progsys/liquidhaskell/issues/1756 (also linked at start of thread)

-- (0)
-- some unsoundness around overflows
[lq|
machineSize :: {v:Int | 0 <= v} |]
machineSize = 9223372036854775807 + 1

[lq|
fixedSize :: {v:Int8 | 0 <= v} |]
fixedSize = 127 + 1
