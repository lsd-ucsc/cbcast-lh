{-# LANGUAGE QuasiQuotes #-}
module Confusions where

import LiquidHaskell (lq)
import Data.Int

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
