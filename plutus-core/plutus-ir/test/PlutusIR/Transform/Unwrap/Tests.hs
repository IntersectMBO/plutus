module PlutusIR.Transform.Unwrap.Tests where

import Test.Tasty
import Test.Tasty.Extras

import PlutusIR.Parser
import PlutusIR.Pass.Test
import PlutusIR.Test
import PlutusIR.Transform.Unwrap

import Data.Functor.Identity
import Test.QuickCheck.Property (Property, withMaxSuccess)

test_unwrap :: TestTree
test_unwrap =
  runTestNested ["plutus-ir", "test", "PlutusIR", "Transform", "Unwrap"] $
    map
      (goldenPir (runIdentity . runTestPass unwrapCancelPass) pTerm)
      [ "unwrapWrap"
      ]

prop_unwrap :: Property
prop_unwrap =
  withMaxSuccess numTestsForPassProp $ testPassProp runIdentity unwrapCancelPass
