module PlutusIR.Transform.EvaluateBuiltins.Tests where

import Test.Tasty
import Test.Tasty.Extras

import PlutusCore.Default.Builtins
import PlutusIR.Analysis.Builtins
import PlutusIR.Parser
import PlutusIR.Properties.Typecheck
import PlutusIR.Test
import PlutusIR.Transform.EvaluateBuiltins
import PlutusPrelude
import Test.QuickCheck.Property (Property, withMaxSuccess)
import Test.Tasty.QuickCheck (testProperty)

test_evaluateBuiltins :: TestTree
test_evaluateBuiltins = runTestNestedIn ["plutus-ir/test/PlutusIR/Transform"] $
    testNested "EvaluateBuiltins" $
        map
            (goldenPir (evaluateBuiltins True def def) pTerm)
            [ "addInteger"
            , "ifThenElse"
            , "trace"
            , "failingBuiltin"
            , "nonConstantArg"
            , "overApplication"
            , "underApplication"
            ]

-- | Check that a term typechecks after a `PlutusIR.Transform.EvaluateBuiltins`
-- pass.
prop_typecheck_evaluateBuiltins :: BuiltinSemanticsVariant DefaultFun -> Property
prop_typecheck_evaluateBuiltins biVariant =
  pure_typecheck_prop (evaluateBuiltins True (BuiltinsInfo biVariant) def)

test_typecheck :: TestTree
test_typecheck = testGroup "typechecking"
  [ testProperty "Builtin Variant 1" $
      withMaxSuccess 3000 (prop_typecheck_evaluateBuiltins DefaultFunSemanticsVariant1)
  , testProperty "Builtin Variant 2" $
      withMaxSuccess 3000 (prop_typecheck_evaluateBuiltins DefaultFunSemanticsVariant2)
  ]
