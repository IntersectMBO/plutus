module PlutusIR.Transform.CommuteFnWithConst.Tests where

import Test.Tasty
import Test.Tasty.Extras

import PlutusIR.Parser
import PlutusIR.Test
import PlutusIR.Transform.CommuteFnWithConst qualified as CommuteFnWithConst

import PlutusIR.Properties.Typecheck
import Test.QuickCheck.Property (withMaxSuccess)
import Test.Tasty.QuickCheck (testProperty)

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

test_typecheck :: TestTree
test_typecheck = testProperty "typechecking" $
      withMaxSuccess 3000 (pure_typecheck_prop CommuteFnWithConst.commuteFnWithConst)
