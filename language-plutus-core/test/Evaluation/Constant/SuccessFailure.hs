module Evaluation.Constant.SuccessFailure
    ( test_applyBuiltinNameSuccessFailure
    ) where

import           Language.PlutusCore.Constant

import           Evaluation.Constant.Apply

import           Test.Tasty
import           Test.Tasty.Hedgehog

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

test_typedConcatenateSuccessFailure :: TestTree
test_typedConcatenateSuccessFailure
    = testProperty "typedConcatenate"
    $ prop_applyBuiltinNameSuccessFailure typedConcatenate (<>)

test_applyBuiltinNameSuccessFailure :: TestTree
test_applyBuiltinNameSuccessFailure =
    testGroup "applyBuiltinNameSuccessFailure"
        [ test_typedAddIntegerSuccessFailure
        , test_typedSubtractIntegerSuccessFailure
        , test_typedMultiplyIntegerSuccessFailure
        , test_typedConcatenateSuccessFailure
        ]
