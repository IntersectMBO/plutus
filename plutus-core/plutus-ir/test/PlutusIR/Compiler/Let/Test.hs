module PlutusIR.Compiler.Let.Test where

import PlutusIR.Test

import Test.Tasty
import Test.Tasty.Extras

test_lets :: TestTree
test_lets = runTestNestedIn ["plutus-ir/test/PlutusIR/Compiler"] $ testNested "Let"
    [ goldenPlcFromPir pTermAsProg "letInLet"
    , goldenPlcFromPir pTermAsProg "letDep"
    ]
