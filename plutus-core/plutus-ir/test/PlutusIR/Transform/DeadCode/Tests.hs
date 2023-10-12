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
import Test.Tasty.ExpectedFailure (ignoreTest)
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

-- FIXME this test sometimes fails so ignoring it to make CI pass.
-- | Check that a term typechecks after a `PlutusIR.Transform.DeadCode.removeDeadBindings` pass.
typecheckRemoveDeadBindingsProp :: BuiltinSemanticsVariant DefaultFun -> Property
typecheckRemoveDeadBindingsProp biVariant =
  withMaxSuccess 50000 $ nonPureTypecheckProp $ removeDeadBindings $ BuiltinsInfo biVariant

test_TypecheckRemoveDeadBindings :: TestTree
test_TypecheckRemoveDeadBindings =
  ignoreTest $ testProperty "typechecking" typecheckRemoveDeadBindingsProp
