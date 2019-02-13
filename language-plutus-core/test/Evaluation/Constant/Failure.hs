{-# LANGUAGE GADTs      #-}
{-# LANGUAGE RankNTypes #-}

module Evaluation.Constant.Failure
    ( test_constantFailure
    ) where

import           Language.PlutusCore.Constant
import           Language.PlutusCore.Generators

import           Evaluation.Constant.Apply

import           Data.Maybe
import           Hedgehog
import           Test.Tasty
import           Test.Tasty.Hedgehog

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

test_applyBuiltinNameFailure :: TestTree
test_applyBuiltinNameFailure =
    testGroup "applyBuiltinNameFailure"
        [ test_typedAddIntegerFailure
        , test_typedMultiplyIntegerFailure
        , test_typedConcatenateFailure
        ]

-- | Generates out-of-bounds constants and checks that their evaluation results in 'EvaluationFailure'.
test_evalOutOfBounds :: TestTree
test_evalOutOfBounds =
    testProperty "evalOutOfBounds" . property $ do
        mayTermWithValue <- forAllPrettyPlcMaybeT $
            withCheckedTermGen genTypedBuiltinOutOfBounds $ \tb mayTermWithValue ->
                -- 'genTypedBuiltinOutOfBounds' only generates out-of-bounds constants for
                -- @integer@s and @bytestring@s, hence we explicitly ignore other built-ins here.
                return $ case tb of
                    TypedBuiltinBool                          -> Nothing
                    TypedBuiltinSized _ TypedBuiltinSizedSize -> Nothing
                    _                                         -> mayTermWithValue
        assert $ isNothing mayTermWithValue

test_constantFailure :: TestTree
test_constantFailure =
    testGroup "constantFailure"
       [ test_applyBuiltinNameFailure
       , test_evalOutOfBounds
       ]
