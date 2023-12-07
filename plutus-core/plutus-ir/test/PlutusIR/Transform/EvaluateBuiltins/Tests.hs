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
test_evaluateBuiltins = runTestNestedIn ["plutus-ir", "test", "PlutusIR", "Transform"] $
    testNested "EvaluateBuiltins" $
      conservative ++ nonConservative
    where
      conservative =
        map
            (goldenPir (evaluateBuiltins True def def) pTerm)
            [ "addInteger"
            , "ifThenElse"
            , "traceConservative"
            , "failingBuiltin"
            , "nonConstantArg"
            , "overApplication"
            , "underApplication"
            , "uncompressBlsConservative"
            ]
      nonConservative =
        map
            (goldenPir (evaluateBuiltins False def def) pTerm)
            -- We want to test the case where this would reduce, i.e.
            [ "traceNonConservative"
            , "uncompressBlsNonConservative"
            , "uncompressAndEqualBlsNonConservative"
            ]

-- | Check that a term typechecks after a `PlutusIR.Transform.EvaluateBuiltins`
-- pass.
prop_TypecheckEvaluateBuiltins ::
    Bool -> BuiltinSemanticsVariant DefaultFun -> Property
prop_TypecheckEvaluateBuiltins conservative biVariant =
  withMaxSuccess 40000 $
    pureTypecheckProp $
        evaluateBuiltins conservative (def {_biSemanticsVariant = biVariant}) def

