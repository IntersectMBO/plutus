module PlutusIR.Transform.CommuteFnWithConst.Tests where

import Test.Tasty
import Test.Tasty.Extras

import PlutusIR.Parser
import PlutusIR.Test
import PlutusIR.Transform.CommuteFnWithConst qualified as CommuteFnWithConst

test_commuteDefaultFun :: TestTree
test_commuteDefaultFun = runTestNestedIn ["plutus-ir/test/PlutusIR/Transform"] $
    testNested "CommuteFnWithConst" $
    map
        (goldenPir CommuteFnWithConst.commuteDefaultFun pTerm)
        [ "equalsInt" -- this tests that the function works on equalInteger
        , "divideInt" -- this tests that the function excludes not commutative functions
        , "multiplyInt" -- this tests that the function works on multiplyInteger
        , "let" -- this tests that it works in the subterms
        ]
