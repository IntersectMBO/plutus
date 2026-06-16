module PlutusIR.Transform.RecInline.Tests where

import Test.Tasty
import Test.Tasty.Extras

import PlutusCore.Default.Builtins ()
import PlutusCore.Quote
import PlutusIR.Analysis.Builtins ()
import PlutusIR.Parser
import PlutusIR.Pass.Test
import PlutusIR.Test
import PlutusIR.Transform.RecInline
import PlutusPrelude
import Test.Tasty.QuickCheck

test_recInline :: TestTree
test_recInline =
  runTestNested ["plutus-ir", "test", "PlutusIR", "Transform", "RecInline"] $
    map
      (goldenPir (runQuote . runTestPass (\tc -> recInlinePassSC def True tc)) pTerm)
      [ "evenOddCollapse"
      , "threeCycleCollapse"
      , "helperStrictAlias"
      , "helperAliasOverApplied"
      , "helperUnderApplied"
      , "bodyUsesBoth"
      , "helperUsedTwice"
      , "pureHelperUsedTwice"
      , "helperSelfRecursive"
      , "sharedHelper"
      , "twoIndependentCycles"
      , "twoIndependentCyclesPartial"
      , "mixedValueBinding"
      , "valueBindingPreventsInlining"
      ]

prop_recInline :: Property
prop_recInline =
  withMaxSuccess numTestsForPassProp $
    testPassProp runQuote $
      \tc -> recInlinePassSC def True tc
