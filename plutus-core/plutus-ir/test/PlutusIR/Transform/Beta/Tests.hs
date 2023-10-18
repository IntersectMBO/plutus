module PlutusIR.Transform.Beta.Tests where

import Test.Tasty
import Test.Tasty.Extras

import PlutusCore qualified as PLC
import PlutusCore.Quote
import PlutusIR.Parser
import PlutusIR.Properties.Typecheck
import PlutusIR.Test
import PlutusIR.Transform.Beta
import Test.QuickCheck.Property (Property, withMaxSuccess)

test_beta :: TestTree
test_beta = runTestNestedIn ["plutus-ir/test/PlutusIR/Transform"] $
    testNested "Beta" $
        map
            (goldenPir (beta . runQuote . PLC.rename) pTerm)
            [ "lamapp"
            , "lamapp2"
            , "absapp"
            , "multiapp"
            , "multilet"
            ]

-- | Check that a term typechecks after a `PlutusIR.Transform.Beta.beta` pass.
prop_TypecheckBeta :: Property
prop_TypecheckBeta = withMaxSuccess 3000 (pureTypecheckProp beta)
