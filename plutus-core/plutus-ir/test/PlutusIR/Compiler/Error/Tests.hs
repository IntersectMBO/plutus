module PlutusIR.Compiler.Error.Tests where

import PlutusIR.Test

import Test.Tasty
import Test.Tasty.Extras

test_error :: TestTree
test_error =
    runTestNestedM ["plutus-ir", "test", "PlutusIR", "Compiler", "Error"] $ do
        goldenPlcFromPir pTermAsProg "mutuallyRecursiveTypes"
        goldenPlcFromPir pTermAsProg "recursiveTypeBind"
