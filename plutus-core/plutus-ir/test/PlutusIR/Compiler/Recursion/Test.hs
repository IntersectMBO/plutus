module PlutusIR.Compiler.Recursion.Test where

import PlutusIR.Test

import Test.Tasty
import Test.Tasty.Extras

test_recursion :: TestTree
test_recursion = runTestNestedIn ["plutus-ir/test/PlutusIR/Compiler"] $ testNested "Recursion"
    [ goldenNamedUPlcFromPir pTermAsProg "factorial"
    , goldenPlcFromPir pTermAsProg "even3"
    , goldenEvalPir pTermAsProg "even3Eval"
    , goldenPlcFromPir pTermAsProg "stupidZero"
    , goldenPlcFromPir pTermAsProg "mutuallyRecursiveValues"
    , goldenEvalPir pTermAsProg "errorBinding"
    ]
