module PlutusIR.Transform.Beta.Tests where

import PlutusCore.Quote
import PlutusIR.Parser
import PlutusIR.Pass.Test
import PlutusIR.Test
import PlutusIR.Transform.Beta
import Test.Cardano.Base.QuickCheck qualified as BaseQC
import Test.QuickCheck.Property (Property)
import Test.Tasty
import Test.Tasty.Extras

test_beta :: TestTree
test_beta =
  runTestNested ["plutus-ir", "test", "PlutusIR", "Transform", "Beta"] $
    map
      (goldenPir (runQuote . runTestPass betaPassSC) pTerm)
      [ "lamapp"
      , "lamapp2"
      , "absapp"
      , "multiapp"
      , "multilet"
      ]

prop_beta :: Property
prop_beta = BaseQC.withNumTests numTestsForPassProp $ testPassProp runQuote betaPassSC
