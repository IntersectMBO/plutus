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

-- FIXME
-- | Check that a term typechecks after a `PlutusIR.Transform.DeadCode.removeDeadBindings` pass.
prop_TypecheckRemoveDeadBindings :: BuiltinSemanticsVariant DefaultFun -> Property
prop_TypecheckRemoveDeadBindings biVariant =
  expectFailure $
    withMaxSuccess 50000 $ nonPureTypecheckProp $ removeDeadBindings $ BuiltinsInfo biVariant
