module PlutusIR.Transform.RecSplit.Tests where

import Test.Tasty
import Test.Tasty.Extras

import Data.Functor.Identity
import PlutusCore.Quote
import PlutusIR.Parser
import PlutusIR.Pass.Test
import PlutusIR.Test
import PlutusIR.Transform.RecSplit
import Test.Tasty.QuickCheck

test_recSplit :: TestTree
test_recSplit =
  runTestNested ["plutus-ir", "test", "PlutusIR", "Transform", "RecSplit"] $
    map
      (goldenPir (runQuote . runTestPass recSplitPass) pTerm)
      [ "truenonrec"
      , "mutuallyRecursiveTypes"
      , "mutuallyRecursiveValues"
      , "selfrecursive"
      , "small"
      , "big"
      ]

prop_recSplit :: Property
prop_recSplit =
  withMaxSuccess numTestsForPassProp $ testPassProp runIdentity recSplitPass
