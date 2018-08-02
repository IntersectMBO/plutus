module Evaluation.Constant.SuccessFailure
    ( test_applyBuiltinNameSuccessFailure
    ) where

import           Language.PlutusCore.Constant
import           Evaluation.Constant.Apply

import           Test.Tasty
import           Test.Tasty.Hedgehog

test_applyBuiltinNameSuccessFailure :: TestTree
test_applyBuiltinNameSuccessFailure =
    -- TODO: fix the divide-by-zero error.
    testGroup "applyBuiltinNameSuccessFailure"
        [ test_typedAddIntegerSuccessFailure
        , test_typedSubtractIntegerSuccessFailure
        , test_typedMultiplyIntegerSuccessFailure
        , test_typedDivideIntegerSuccessFailure
        , test_typedRemainderIntegerSuccessFailure
        , test_typedLessThanIntegerSuccessFailure
        , test_typedLessThanEqIntegerSuccessFailure
        , test_typedGreaterThanIntegerSuccessFailure
        , test_typedGreaterThanEqIntegerSuccessFailure
        , test_typedEqIntegerSuccessFailure
        , test_typedResizeIntegerSuccessFailure
        ]

test_typedAddIntegerSuccessFailure :: TestTree
test_typedAddIntegerSuccessFailure
    = testProperty "typedAddInteger"
    $ prop_applyBuiltinNameSuccessFailure typedAddInteger (+)

test_typedSubtractIntegerSuccessFailure :: TestTree
test_typedSubtractIntegerSuccessFailure
    = testProperty "typedSubtractInteger"
    $ prop_applyBuiltinNameSuccessFailure typedSubtractInteger (-)

test_typedMultiplyIntegerSuccessFailure :: TestTree
test_typedMultiplyIntegerSuccessFailure
    = testProperty "typedMultiplyInteger"
    $ prop_applyBuiltinNameSuccessFailure typedMultiplyInteger (*)

test_typedDivideIntegerSuccessFailure :: TestTree
test_typedDivideIntegerSuccessFailure
    = testProperty "typedDivideInteger"
    $ prop_applyBuiltinNameSuccessFailure typedDivideInteger div

test_typedRemainderIntegerSuccessFailure :: TestTree
test_typedRemainderIntegerSuccessFailure
    = testProperty "typedRemainderInteger"
    $ prop_applyBuiltinNameSuccessFailure typedRemainderInteger mod

test_typedLessThanIntegerSuccessFailure :: TestTree
test_typedLessThanIntegerSuccessFailure
    = testProperty "typedLessThanInteger"
    $ prop_applyBuiltinNameSuccessFailure typedLessThanInteger (<)

test_typedLessThanEqIntegerSuccessFailure :: TestTree
test_typedLessThanEqIntegerSuccessFailure
    = testProperty "typedLessThanEqInteger"
    $ prop_applyBuiltinNameSuccessFailure typedLessThanEqInteger (<=)

test_typedGreaterThanIntegerSuccessFailure :: TestTree
test_typedGreaterThanIntegerSuccessFailure
    = testProperty "typedGreaterThanInteger"
    $ prop_applyBuiltinNameSuccessFailure typedGreaterThanInteger (>)

test_typedGreaterThanEqIntegerSuccessFailure :: TestTree
test_typedGreaterThanEqIntegerSuccessFailure
    = testProperty "typedGreaterThanEqInteger"
    $ prop_applyBuiltinNameSuccessFailure typedGreaterThanEqInteger (>=)

test_typedEqIntegerSuccessFailure :: TestTree
test_typedEqIntegerSuccessFailure
    = testProperty "typedEqInteger"
    $ prop_applyBuiltinNameSuccessFailure typedEqInteger (==)

test_typedResizeIntegerSuccessFailure :: TestTree
test_typedResizeIntegerSuccessFailure
    = testProperty "typedResizeInteger"
    $ prop_applyBuiltinNameSuccessFailure typedResizeInteger (const id)


{-
    , typedConcatenate
    , typedTakeByteString
    , typedDropByteString
    , typedEqByteString
-}
