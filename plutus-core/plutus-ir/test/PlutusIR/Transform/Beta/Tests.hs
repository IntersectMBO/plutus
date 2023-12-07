module PlutusIR.Transform.Beta.Tests where

import Test.Tasty
import Test.Tasty.Extras

import Data.Functor.Identity
import PlutusIR.Parser
import PlutusIR.Pass.Test
import PlutusIR.Test
import PlutusIR.Transform.Beta
import Test.QuickCheck.Property (Property, withMaxSuccess)

test_beta :: TestTree
test_beta = runTestNestedIn ["plutus-ir", "test", "PlutusIR", "Transform"] $
    testNested "Beta" $
        map
            (goldenPir (runIdentity . runTestPass betaPass) pTerm)
            [ "lamapp"
            , "lamapp2"
            , "absapp"
            , "multiapp"
            , "multilet"
            ]

prop_beta :: Property
prop_beta = withMaxSuccess numTestsForPassProp $ testPassProp runIdentity betaPass
