module PlutusIR.Transform.CommuteFnWithConst.Tests where

import Test.Tasty
import Test.Tasty.Extras

import PlutusIR.Parser
import PlutusIR.Test
import PlutusIR.Transform.CommuteFnWithConst

import PlutusIR.Properties.Typecheck
import Test.QuickCheck.Property (Property, withMaxSuccess)

test_commuteDefaultFun :: TestTree
test_commuteDefaultFun = runTestNestedIn ["plutus-ir", "test", "PlutusIR", "Transform"] $
    testNested "CommuteFnWithConst" $
    map
        (goldenPir commuteDefaultFun pTerm)
        [ "equalsInt" -- this tests that the function works on equalInteger
        , "divideInt" -- this tests that the function excludes not commutative functions
        , "multiplyInt" -- this tests that the function works on multiplyInteger
        , "let" -- this tests that it works in the subterms
        ]

-- | Check that a term typechecks after a `PlutusIR.Transform.CommuteFnWithConst.commuteFnWithConst`
-- pass.
prop_TypecheckCommuteFnWithConst :: Property
prop_TypecheckCommuteFnWithConst =
      withMaxSuccess 3000 (pureTypecheckProp commuteFnWithConst)
