module PlutusIR.Transform.RecSplit.Tests where

import Test.Tasty
import Test.Tasty.Extras

import PlutusCore qualified as PLC
import PlutusCore.Quote
import PlutusIR.Parser
import PlutusIR.Test
import PlutusIR.Transform.RecSplit qualified as RecSplit

test_recSplit :: TestTree
test_recSplit = runTestNestedIn ["plutus-ir/test/PlutusIR/Transform"] $
    testNested "RecSplit" $
        map
            (goldenPir (RecSplit.recSplit . runQuote . PLC.rename) pTerm)
            [ "truenonrec"
            , "mutuallyRecursiveTypes"
            , "mutuallyRecursiveValues"
            , "selfrecursive"
            , "small"
            , "big"
            ]
