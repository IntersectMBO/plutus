{-# LANGUAGE OverloadedStrings #-}
module Evaluation.CkMachine
    ( test_evaluateCk
    ) where

import           Language.PlutusCore
import           Language.PlutusCore.Constant
import           Language.PlutusCore.Evaluation.CkMachine
import           Language.PlutusCore.Generators
import           Language.PlutusCore.Generators.Interesting
import           Language.PlutusCore.Generators.Test

import           Hedgehog                                   hiding (Size, Var)
import           Test.Tasty
import           Test.Tasty.Hedgehog

propEvaluateCk :: GenT Quote (TermOf (TypedBuiltinValue Size a)) -> Property
propEvaluateCk = propEvaluate evaluateCk

-- | Generate an 'Integer', turn it into a Scott-encoded PLC @Nat@ (see 'getBuiltinNat'),
-- turn that @Nat@ into the corresponding PLC @integer@ using a fold (see 'getBuiltinFoldNat')
-- defined in terms of generic fix (see 'getBuiltinFix'), feed the resulting 'Term' to the CK machine
-- (see 'evaluateCk') and check that the original 'Integer' and the computed @integer@ are in sync.
prop_NatRoundtrip :: Property
prop_NatRoundtrip = propEvaluateCk genNatRoundtrip

-- | Generate a list of 'Integer's, turn it into a Scott-encoded PLC @List@ (see 'getBuiltinList'),
-- sum elements of the list (see 'getBuiltinSum'), feed the resulting 'Term' to the CK machine
-- (see 'evaluateCk') and check that 'sum' applied to the original list is in sync with the computed sum.
prop_ListSum :: Property
prop_ListSum = propEvaluateCk genListSum

-- | Generate a @boolean@ and two @integer@s and check whether @if b then i1 else i2@
-- means the same thing in Haskell and PLC. Terms are generated using 'genTermLoose'.
prop_ifIntegers :: Property
prop_ifIntegers = propEvaluateCk genIfIntegers

test_evaluateCk :: TestTree
test_evaluateCk = testGroup "evaluateCk"
    [ testProperty "prop_NatRoundtrip" prop_NatRoundtrip
    , testProperty "prop_ListSum"      prop_ListSum
    , testProperty "prop_ifIntegers"   prop_ifIntegers
    ]
