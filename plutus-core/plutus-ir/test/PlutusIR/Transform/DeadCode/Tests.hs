module PlutusIR.Transform.DeadCode.Tests where

import Test.Tasty
import Test.Tasty.Extras

import PlutusCore.Quote
import PlutusIR.Parser
import PlutusIR.Test
import PlutusIR.Transform.DeadCode qualified as DeadCode
import PlutusPrelude

test_deadCode :: TestTree
test_deadCode = runTestNestedIn ["plutus-ir/test/PlutusIR/Transform"] $
    testNested "DeadCode" $
        map
            (goldenPir (runQuote . DeadCode.removeDeadBindings def) pTerm)
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
