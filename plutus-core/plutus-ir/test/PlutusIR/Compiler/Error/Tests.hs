module PlutusIR.Compiler.Error.Tests where

import PlutusIR.Test

import Test.Tasty
import Test.Tasty.Extras

test_error :: TestTree
test_error =
  runTestNested
    ["plutus-ir", "test", "PlutusIR", "Compiler", "Error"]
    [ goldenPlcFromPir pTermAsProg "mutuallyRecursiveTypes"
    , goldenPlcFromPir pTermAsProg "recursiveTypeBind"
    ]
