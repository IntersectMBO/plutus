module PlutusIR.Transform.Beta.Tests where

import Test.Tasty
import Test.Tasty.Extras

import PlutusCore qualified as PLC
import PlutusCore.Quote
import PlutusIR.Parser
import PlutusIR.Test
import PlutusIR.Transform.Beta qualified as Beta

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
