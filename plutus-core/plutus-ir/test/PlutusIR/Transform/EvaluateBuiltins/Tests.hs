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
prop_TypecheckEvaluateBuiltins ::
    Bool -> BuiltinSemanticsVariant DefaultFun -> Property
prop_TypecheckEvaluateBuiltins conservative biVariant =
  withMaxSuccess 40000 $
    pureTypecheckProp $
        evaluateBuiltins conservative (BuiltinsInfo biVariant defaultUniMatcherLike) def

