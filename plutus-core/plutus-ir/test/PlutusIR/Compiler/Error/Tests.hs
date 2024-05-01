module PlutusIR.Compiler.Error.Tests where

import PlutusIR.Test

import Test.Tasty
import Test.Tasty.Extras

test_error :: TestTree
test_error =
    runTestNestedIn ["plutus-ir", "test", "PlutusIR", "Compiler"] . testNestedM "Error" $ do
        goldenPlcFromPir pTermAsProg "mutuallyRecursiveTypes"
        goldenPlcFromPir pTermAsProg "recursiveTypeBind"
