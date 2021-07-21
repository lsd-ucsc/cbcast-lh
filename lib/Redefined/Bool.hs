module Redefined.Bool where

{-@ reflect boolAnd @-}
{-@ boolAnd :: a:Bool -> b:Bool -> {c:Bool | c <=> a && b} @-}
boolAnd :: Bool -> Bool -> Bool
boolAnd True True = True
boolAnd _ _ = False

{-@ reflect boolOr @-}
{-@ boolOr :: a:Bool -> b:Bool -> {c:Bool | c <=> a || b} @-}
boolOr :: Bool -> Bool -> Bool
boolOr True _ = True
boolOr _ True = True
boolOr _ _ = False
