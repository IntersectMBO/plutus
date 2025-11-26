module PlutusIR.Transform.KnownCon.Tests where

import Test.Tasty
import Test.Tasty.Extras

import PlutusCore.Quote
import PlutusIR.Parser
import PlutusIR.Pass.Test
import PlutusIR.Test
import PlutusIR.Transform.KnownCon qualified as KnownCon
import Test.QuickCheck

test_knownCon :: TestTree
test_knownCon =
  runTestNested ["plutus-ir", "test", "PlutusIR", "Transform", "KnownCon"] $
    map
      (goldenPir (runQuote . runTestPass KnownCon.knownConPassSC) pTerm)
      [ "applicative"
      , "bool"
      , "list"
      , "maybe-just"
      , "maybe-just-unsaturated"
      , "maybe-nothing"
      , "pair"
      ]

prop_knownCon :: Property
prop_knownCon = withMaxSuccess numTestsForPassProp $ testPassProp runQuote KnownCon.knownConPassSC
