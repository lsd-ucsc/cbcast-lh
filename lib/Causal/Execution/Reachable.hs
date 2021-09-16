{-# OPTIONS_GHC "-Wno-unused-imports" #-} -- LH needs the qualified imports for SMT things
module Causal.Execution.Reachable where
-- Definition of a well-formed execution using the semantics.

import Language.Haskell.Liquid.ProofCombinators

import Redefined.Proof
import qualified Redefined.Tuple
import qualified Redefined.Function
import Redefined.List
import qualified Redefined.Set

import Data.Maybe (isJust)
import qualified Data.Assoc
import qualified Data.BinaryRelation

import Causal.Execution.Type
import Causal.Execution.Semantics

-- | Apply rules via the semantics in foldr/cons-order to obtain a final
-- execution, unless the premises of some rule for some intermediate execution
-- do not hold.
--
-- NOTE: (foldr f x [a,b,c]) is like (f a (f b (f c x)))
{-@ reflect applyRules @-}
applyRules :: (Ord p, Ord m) => [Rule p m] -> Maybe (Execution p m)
applyRules rules = listFoldr applyRulesHelper (Just execution0) rules

-- | Apply the rule via the semantics to the execution, unless the premises do
-- not hold or there's already no execution.
{-@ reflect applyRulesHelper @-}
applyRulesHelper :: (Ord p, Ord m) => Rule p m -> Maybe (Execution p m) -> Maybe (Execution p m)
applyRulesHelper _rule Nothing = Nothing
applyRulesHelper rule (Just x) =
    if premisesHold rule x
    then Just (semantics rule x)
    else Nothing

-- | Rules which produce an execution because the premises hold at each step.
-- The head is the last rule applied, the tail represents the prior execution.
{-@
type ValidRules p m =
    { rules : [Rule p m] | isJust (applyRules rules) }
@-}

-- | Unconditionally obtain an execution from a valid sequenc of rules.
{-@ reflect applyValidRules @-}
{-@ applyValidRules :: ValidRules p m -> Execution p m @-}
applyValidRules :: (Ord p, Ord m) => [Rule p m] -> Execution p m
applyValidRules rules = case applyRules rules of
    Just execution -> execution

{-@ ple validRulesTailValid @-} -- Required to prevent an LH crash
{-@
validRulesTailValid
    :: { rules : ValidRules p m | rules /= [] }
    -> { isJust (applyRules (tail rules)) }
@-}
validRulesTailValid :: (Ord p, Ord m) => [Rule p m] -> Proof
validRulesTailValid (r:rs) = case applyRules rs of
    Just _execution -> () *** QED
    Nothing
        ->  isJust (applyRules (r:rs)) -- premise
        === isJust (applyRulesHelper r (applyRules rs))
        === isJust (applyRulesHelper r Nothing) -- by the case split
        === isJust Nothing -- contradiction
        *** QED

---- -- Causes LH crash
---- -- | Add the assertion everywhere that the tail of non-empty valid rules is
---- -- valid.
---- {-@
---- using [Rule p m] as
----     { rules : [Rule p m] |
----         isJust (applyRules rules) && rules /= []
----             => isJust (applyRules (tail rules))
----     }
---- @-}

-- | Obtain the penultimate step in a sequence of valid rule applications.
{-@ reflect validRulesTail @-}
{-@ validRulesTail :: {rules:ValidRules p m | rules /= []} -> ValidRules p m @-}
validRulesTail :: (Ord p, Ord m) => [Rule p m] -> [Rule p m]
validRulesTail (r:rs) = rs `proofConst` validRulesTailValid (r:rs)

{-@ ple rulesEx0 @-}
{-@ rulesEx0 :: ValidRules p m @-}
rulesEx0 :: [Rule p m]
rulesEx0 = []

{-@ ple rulesEx1 @-}
{-@ rulesEx1 :: ValidRules Int String @-}
rulesEx1 :: [Rule Int String]
rulesEx1 = [BroadcastRule 1 "hello world"]

{-@ ple rulesEx2 @-}
{-@ rulesEx2 :: ValidRules Int String @-}
rulesEx2 :: [Rule Int String]
rulesEx2 = tail [BroadcastRule 1 "hello world"]

---- -- LH doesn't know that rulesEx1 /= [] ??
---- {-@ ple rulesEx3 @-}
---- {-@ rulesEx3 :: ValidRules Int String @-}
---- rulesEx3 :: [Rule Int String]
---- rulesEx3 = validRulesTail rulesEx1
