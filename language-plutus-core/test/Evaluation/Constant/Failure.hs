module Evaluation.Constant.Failure
    ( test_applyBuiltinNameFailure
    ) where

import           Language.PlutusCore.Constant
import           Language.PlutusCore.Generators

import           Evaluation.Constant.Apply

import           Data.Semigroup
import           Test.Tasty
import           Test.Tasty.Hedgehog

test_applyBuiltinNameFailure :: TestTree
test_applyBuiltinNameFailure =
    testGroup "applyBuiltinNameFailure"
        [ test_typedAddIntegerFailure
        , test_typedMultiplyIntegerFailure
        , test_typedConcatenateFailure
        ]

test_typedAddIntegerFailure :: TestTree
test_typedAddIntegerFailure
    = testProperty "typedAddInteger"
    $ prop_applyBuiltinNameFailure typedAddInteger (+) genTypedBuiltinAddFailure

test_typedMultiplyIntegerFailure :: TestTree
test_typedMultiplyIntegerFailure
    = testProperty "typedMultiplyInteger"
    $ prop_applyBuiltinNameFailure typedMultiplyInteger (*) genTypedBuiltinMultiplyFailure

test_typedConcatenateFailure :: TestTree
test_typedConcatenateFailure
    = testProperty "typedConcatenate"
    $ prop_applyBuiltinNameFailure typedConcatenate (<>) genTypedBuiltinConcatenateFailure
