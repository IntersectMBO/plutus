module PlutusIR.Transform.RecInline.Tests where

import Test.Tasty
import Test.Tasty.Extras

import PlutusCore.Quote
import PlutusIR.Parser
import PlutusIR.Pass.Test
import PlutusIR.Test
import PlutusIR.Transform.RecInline
import Test.Tasty.QuickCheck

test_recInline :: TestTree
test_recInline =
  runTestNested ["plutus-ir", "test", "PlutusIR", "Transform", "RecInline"] $
    map
      (goldenPir (runQuote . runTestPass recInlinePassSC) pTerm)
      [ "evenOddCollapse"
      , "threeCycleCollapse"
      , "helperStrictAlias"
      , "bodyUsesBoth"
      , "helperUsedTwice"
      , "helperSelfRecursive"
      , "sharedHelper"
      ]

prop_recInline :: Property
prop_recInline =
  withMaxSuccess numTestsForPassProp $ testPassProp runQuote recInlinePassSC
