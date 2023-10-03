module PlutusIR.Transform.Beta.Tests where

import Test.Tasty
import Test.Tasty.Extras

import PlutusCore qualified as PLC
import PlutusCore.Quote
import PlutusIR.Parser
import PlutusIR.Properties.Typecheck
import PlutusIR.Test
import PlutusIR.Transform.Beta qualified as Beta
import Test.QuickCheck.Property (withMaxSuccess)
import Test.Tasty.QuickCheck (testProperty)

test_beta :: TestTree
test_beta = runTestNestedIn ["plutus-ir/test/PlutusIR/Transform"] $
    testNested "Beta" $
        map
            (goldenPir (Beta.beta . runQuote . PLC.rename) pTerm)
            [ "lamapp"
            , "lamapp2"
            , "absapp"
            , "multiapp"
            , "multilet"
            ]

test_typecheck :: TestTree
test_typecheck = testProperty "typechecking" $
    withMaxSuccess 3000 (pure_typecheck_prop Beta.beta)
