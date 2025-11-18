module PlutusIR.Transform.LetFloatIn.Tests where

import Test.Tasty
import Test.Tasty.Extras

import PlutusCore qualified as PLC
import PlutusCore.Builtin
import PlutusCore.Quote
import PlutusIR.Analysis.Builtins
import PlutusIR.Parser
import PlutusIR.Pass.Test
import PlutusIR.Test
import PlutusIR.Transform.LetFloatIn qualified as LetFloatIn
import PlutusIR.Transform.LetMerge qualified as LetMerge
import PlutusIR.Transform.Rename ()
import PlutusPrelude
import Test.QuickCheck.Property (Property, withMaxSuccess)

test_letFloatInConservative :: TestTree
test_letFloatInConservative =
  runTestNested ["plutus-ir", "test", "PlutusIR", "Transform", "LetFloatIn", "conservative"] $
    map
      (goldenPir (runQuote . runTestPass testPass) pTerm)
      [ "avoid-floating-into-lam"
      , "avoid-floating-into-tyabs"
      ]
  where
    testPass tcconfig =
      LetFloatIn.floatTermPassSC tcconfig def False
        <> LetMerge.letMergePass tcconfig

test_letFloatInRelaxed :: TestTree
test_letFloatInRelaxed =
  runTestNested ["plutus-ir", "test", "PlutusIR", "Transform", "LetFloatIn", "relaxed"] $
    map
      (goldenPir (runQuote . runTestPass testPass) pTerm)
      [ "avoid-floating-into-RHS"
      , "avoid-moving-strict-nonvalue-bindings"
      , "cannot-float-into-app"
      , "datatype1"
      , "datatype2"
      , "float-into-fun-and-arg-1"
      , "float-into-fun-and-arg-2"
      , "float-into-lam1"
      , "float-into-lam2"
      , "float-into-RHS"
      , "float-into-tyabs1"
      , "float-into-tyabs2"
      , "float-into-constr"
      , "float-into-case-arg"
      , "float-into-case-branch"
      , "type"
      ]
  where
    testPass tcconfig =
      LetFloatIn.floatTermPassSC tcconfig def True
        <> LetMerge.letMergePass tcconfig

prop_floatIn
  :: BuiltinSemanticsVariant PLC.DefaultFun -> Bool -> Property
prop_floatIn biVariant conservative =
  withMaxSuccess numTestsForPassProp $ testPassProp runQuote testPass
  where
    testPass tcconfig =
      LetFloatIn.floatTermPassSC
        tcconfig
        (def {_biSemanticsVariant = biVariant})
        conservative
