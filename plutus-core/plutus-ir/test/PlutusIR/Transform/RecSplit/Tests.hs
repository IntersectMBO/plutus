module PlutusIR.Transform.RecSplit.Tests where

import Test.Tasty
import Test.Tasty.Extras

import PlutusCore qualified as PLC
import PlutusCore.Quote
import PlutusIR.Parser
import PlutusIR.Properties.Typecheck
import PlutusIR.Test
import PlutusIR.Transform.RecSplit
import Test.Tasty.QuickCheck

test_recSplit :: TestTree
test_recSplit = runTestNestedIn ["plutus-ir/test/PlutusIR/Transform"] $
    testNested "RecSplit" $
        map
            (goldenPir (recSplit . runQuote . PLC.rename) pTerm)
            [ "truenonrec"
            , "mutuallyRecursiveTypes"
            , "mutuallyRecursiveValues"
            , "selfrecursive"
            , "small"
            , "big"
            ]

test_typecheck :: TestTree
test_typecheck = testProperty "typechecking" $
  withMaxSuccess 3000 (pure_typecheck_prop recSplit)
