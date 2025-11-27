module PlutusIR.Transform.EvaluateBuiltins.Tests where

import Test.Tasty
import Test.Tasty.Extras

import Data.Functor.Identity
import PlutusCore.Default.Builtins
import PlutusIR.Analysis.Builtins
import PlutusIR.Parser
import PlutusIR.Pass.Test
import PlutusIR.Test
import PlutusIR.Transform.EvaluateBuiltins
import PlutusPrelude
import Test.QuickCheck.Property (Property, withMaxSuccess)

test_evaluateBuiltins :: TestTree
test_evaluateBuiltins =
  runTestNested ["plutus-ir", "test", "PlutusIR", "Transform", "EvaluateBuiltins"] $
    conservative ++ nonConservative
  where
    conservative =
      map
        ( goldenPir
            (runIdentity . runTestPass (\tc -> evaluateBuiltinsPass tc True def def))
            pTerm
        )
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

prop_evaluateBuiltins :: Bool -> BuiltinSemanticsVariant DefaultFun -> Property
prop_evaluateBuiltins conservative biVariant =
  withMaxSuccess numTestsForPassProp
    $ testPassProp
      runIdentity
    $ \tc -> evaluateBuiltinsPass tc conservative (def {_biSemanticsVariant = biVariant}) def
