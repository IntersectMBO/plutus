{-# LANGUAGE TypeApplications #-}

module PlutusIR.Transform.LetFloatOut.Tests where

import Test.Tasty
import Test.Tasty.Extras

import PlutusCore qualified as PLC
import PlutusCore.Builtin
import PlutusCore.Quote
import PlutusIR.Analysis.Builtins
import PlutusIR.Parser
import PlutusIR.Pass.Test
import PlutusIR.Test
import PlutusIR.Transform.LetFloatOut qualified as LetFloatOut
import PlutusIR.Transform.LetMerge qualified as LetMerge
import PlutusIR.Transform.RecSplit qualified as RecSplit
import PlutusIR.Transform.Rename ()
import PlutusPrelude
import Test.QuickCheck.Property (Property, withMaxSuccess)

test_letFloatOut :: TestTree
test_letFloatOut =
  runTestNested ["plutus-ir", "test", "PlutusIR", "Transform", "LetFloatOut"] $
    map
      (goldenPir (runQuote . runTestPass testPass) pTerm)
      [ "letInLet"
      , "listMatch"
      , "maybe"
      , "ifError"
      , "mutuallyRecursiveTypes"
      , "mutuallyRecursiveValues"
      , "nonrec1"
      , "nonrec2"
      , "nonrec3"
      , "nonrec4"
      , "nonrec6"
      , "nonrec7"
      , "nonrec8"
      , "nonrec9"
      , "rec1"
      , "rec2"
      , "rec3"
      , "rec4"
      , "nonrecToRec"
      , "nonrecToNonrec"
      , "oldLength"
      , "strictValue"
      , "strictNonValue"
      , "strictNonValue2"
      , "strictNonValue3"
      , "strictValueNonValue"
      , "strictValueValue"
      , "even3Eval"
      , "strictNonValueDeep"
      , "oldFloatBug"
      , "outRhs"
      , "outLam"
      , "inLam"
      , "rhsSqueezeVsNest"
      ]
  where
    testPass tcconfig =
      LetFloatOut.floatTermPassSC tcconfig def
        <> RecSplit.recSplitPass tcconfig
        <> LetMerge.letMergePass tcconfig

prop_floatOut :: BuiltinSemanticsVariant PLC.DefaultFun -> Property
prop_floatOut biVariant = withMaxSuccess numTestsForPassProp $ testPassProp runQuote testPass
  where
    testPass tcconfig =
      LetFloatOut.floatTermPassSC
        tcconfig
        (def {_biSemanticsVariant = biVariant})
