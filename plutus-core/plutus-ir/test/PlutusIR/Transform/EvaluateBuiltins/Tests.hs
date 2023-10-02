module PlutusIR.Transform.EvaluateBuiltins.Tests where

import Test.Tasty
import Test.Tasty.Extras

import PlutusIR.Parser
import PlutusIR.Test
import PlutusIR.Transform.EvaluateBuiltins qualified as EvaluateBuiltins
import PlutusPrelude

test_evaluateBuiltins :: TestTree
test_evaluateBuiltins = runTestNestedIn ["plutus-ir/test/PlutusIR/Transform"] $
    testNested "EvaluateBuiltins" $
        map
            (goldenPir (EvaluateBuiltins.evaluateBuiltins True def def) pTerm)
            [ "addInteger"
            , "ifThenElse"
            , "trace"
            , "failingBuiltin"
            , "nonConstantArg"
            , "overApplication"
            , "underApplication"
            ]
