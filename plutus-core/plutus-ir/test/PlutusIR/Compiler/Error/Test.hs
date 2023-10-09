module PlutusIR.Compiler.Error.Test where

import PlutusIR.Test

import Test.Tasty
import Test.Tasty.Extras

test_error :: TestTree
test_error = runTestNestedIn ["plutus-ir/test/PlutusIR/Compiler"] $ testNested "Error"
    [ goldenPlcFromPir pTermAsProg "mutuallyRecursiveTypes"
    , goldenPlcFromPir pTermAsProg "recursiveTypeBind"
    ]
