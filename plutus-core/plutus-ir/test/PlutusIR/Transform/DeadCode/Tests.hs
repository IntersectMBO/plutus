module PlutusIR.Transform.DeadCode.Tests where

import Test.Tasty
import Test.Tasty.Extras

import PlutusCore.Default
import PlutusCore.Quote
import PlutusIR.Analysis.Builtins
import PlutusIR.Parser
import PlutusIR.Properties.Typecheck
import PlutusIR.Test
import PlutusIR.Transform.DeadCode
import PlutusPrelude
import Test.Tasty.ExpectedFailure (expectFail)
import Test.Tasty.QuickCheck

test_deadCode :: TestTree
test_deadCode = runTestNestedIn ["plutus-ir/test/PlutusIR/Transform"] $
    testNested "DeadCode" $
        map
            (goldenPir (runQuote . removeDeadBindings def) pTerm)
            [ "typeLet"
            , "termLet"
            , "strictLet"
            , "nonstrictLet"
            , "datatypeLiveType"
            , "datatypeLiveConstr"
            , "datatypeLiveDestr"
            , "datatypeDead"
            , "singleBinding"
            , "builtinBinding"
            , "etaBuiltinBinding"
            , "nestedBindings"
            , "nestedBindingsIndirect"
            , "recBindingSimple"
            , "recBindingComplex"
            , "pruneDatatype"
            ]

test_typecheck :: TestTree
test_typecheck = testGroup "typechecking"
  [ testProperty "Builtin Variant1" $
  withMaxSuccess 5000
  (non_pure_typecheck_prop (removeDeadBindings (BuiltinsInfo DefaultFunSemanticsVariant1)))

  -- FIXME this test mostly pass, but sometimes fail. Test many times to make it fail consistently.
  , expectFail $ testProperty "Builtin Variant2" $
  withMaxSuccess 10000
  (non_pure_typecheck_prop (removeDeadBindings (BuiltinsInfo DefaultFunSemanticsVariant2)))
  ]
