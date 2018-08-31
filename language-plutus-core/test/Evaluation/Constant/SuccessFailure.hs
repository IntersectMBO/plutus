module Evaluation.Constant.SuccessFailure
    ( test_applyBuiltinNameSuccessFailure
    ) where

import           Evaluation.Constant.Apply
import           Language.PlutusCore.Constant

import           Data.Semigroup
import           Test.Tasty
import           Test.Tasty.Hedgehog

test_applyBuiltinNameSuccessFailure :: TestTree
test_applyBuiltinNameSuccessFailure =
    testGroup "applyBuiltinNameSuccessFailure"
        [ test_typedAddIntegerSuccessFailure
        , test_typedSubtractIntegerSuccessFailure
        , test_typedMultiplyIntegerSuccessFailure
        , test_typedResizeIntegerSuccessFailure
        , test_typedConcatenateSuccessFailure
        , test_typedResizeByteStringSuccessFailure
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

test_typedResizeIntegerSuccessFailure :: TestTree
test_typedResizeIntegerSuccessFailure
    = testProperty "typedResizeInteger"
    $ prop_applyBuiltinNameSuccessFailure typedResizeInteger (const id)

test_typedConcatenateSuccessFailure :: TestTree
test_typedConcatenateSuccessFailure
    = testProperty "typedConcatenate"
    $ prop_applyBuiltinNameSuccessFailure typedConcatenate (<>)

test_typedResizeByteStringSuccessFailure :: TestTree
test_typedResizeByteStringSuccessFailure
    = testProperty "typedResizeByteString"
    $ prop_applyBuiltinNameSuccessFailure typedResizeByteString (const id)
