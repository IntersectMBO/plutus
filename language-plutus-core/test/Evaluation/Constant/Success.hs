module Evaluation.Constant.Success
    ( test_applyBuiltinNameSuccess
    ) where

import           Evaluation.Constant.Apply
import           Language.PlutusCore.Constant
import           Language.PlutusCore.TestSupport

import qualified Data.ByteString.Lazy            as BSL
import           Data.Semigroup
import qualified Hedgehog.Gen                    as Gen
import qualified Hedgehog.Range                  as Range
import           Test.Tasty
import           Test.Tasty.Hedgehog

test_applyBuiltinNameSuccess :: TestTree
test_applyBuiltinNameSuccess =
    testGroup "applyBuiltinNameSuccess"
        [ test_typedAddIntegerSuccess
        , test_typedSubtractIntegerSuccess
        , test_typedMultiplyIntegerSuccess
        , test_typedDivideIntegerSuccess
        , test_typedRemainderIntegerSuccess
        , test_typedLessThanIntegerSuccess
        , test_typedLessThanEqIntegerSuccess
        , test_typedGreaterThanIntegerSuccess
        , test_typedGreaterThanEqIntegerSuccess
        , test_typedEqIntegerSuccess
        , test_typedConcatenateSuccess
        , test_typedTakeByteStringSuccess
        , test_typedDropByteStringSuccess
        , test_typedEqByteStringSuccess
        ]

test_typedAddIntegerSuccess :: TestTree
test_typedAddIntegerSuccess
    = testProperty "typedAddInteger"
    $ prop_applyBuiltinNameSuccess typedAddInteger (+)
    $ genTypedBuiltinSum

test_typedSubtractIntegerSuccess :: TestTree
test_typedSubtractIntegerSuccess
    = testProperty "typedSubtractInteger"
    $ prop_applyBuiltinNameSuccess typedSubtractInteger (-)
    $ genTypedBuiltinSum

test_typedMultiplyIntegerSuccess :: TestTree
test_typedMultiplyIntegerSuccess
    = testProperty "typedMultiplyInteger"
    $ prop_applyBuiltinNameSuccess typedMultiplyInteger (*)
    $ updateTypedBuiltinGenInt
          (\low high -> Gen.integral $ Range.linear (negate . isqrt . abs $ low) (isqrt high))
    $ genTypedBuiltinDef

test_typedDivideIntegerSuccess :: TestTree
test_typedDivideIntegerSuccess
    = testProperty "typedDivideInteger"
    $ prop_applyBuiltinNameSuccess typedDivideInteger div
    $ genTypedBuiltinDiv

test_typedRemainderIntegerSuccess :: TestTree
test_typedRemainderIntegerSuccess
    = testProperty "typedRemainderInteger"
    $ prop_applyBuiltinNameSuccess typedRemainderInteger mod
    $ genTypedBuiltinDiv

test_typedLessThanIntegerSuccess :: TestTree
test_typedLessThanIntegerSuccess
    = testProperty "typedLessThanInteger"
    $ prop_applyBuiltinNameSuccess typedLessThanInteger (<)
    $ genTypedBuiltinDef

test_typedLessThanEqIntegerSuccess :: TestTree
test_typedLessThanEqIntegerSuccess
    = testProperty "typedLessThanEqInteger"
    $ prop_applyBuiltinNameSuccess typedLessThanEqInteger (<=)
    $ genTypedBuiltinDef

test_typedGreaterThanIntegerSuccess :: TestTree
test_typedGreaterThanIntegerSuccess
    = testProperty "typedGreaterThanInteger"
    $ prop_applyBuiltinNameSuccess typedGreaterThanInteger (>)
    $ genTypedBuiltinDef

test_typedGreaterThanEqIntegerSuccess :: TestTree
test_typedGreaterThanEqIntegerSuccess
    = testProperty "typedGreaterThanEqInteger"
    $ prop_applyBuiltinNameSuccess typedGreaterThanEqInteger (>=)
    $ genTypedBuiltinDef

test_typedEqIntegerSuccess :: TestTree
test_typedEqIntegerSuccess
    = testProperty "typedEqInteger"
    $ prop_applyBuiltinNameSuccess typedEqInteger (==)
    $ genTypedBuiltinDef

test_typedConcatenateSuccess :: TestTree
test_typedConcatenateSuccess
    = testProperty "typedConcatenate"
    $ prop_applyBuiltinNameSuccess typedConcatenate (<>)
    $ updateTypedBuiltinGenBS
          -- TODO 'Gen.bytes' is probably inappropriate.
          (\high -> fmap BSL.fromStrict . Gen.bytes $ Range.linear 0 (high `div` 2))
    $ genTypedBuiltinDef

test_typedTakeByteStringSuccess :: TestTree
test_typedTakeByteStringSuccess
    = testProperty "typedTakeByteString"
    $ prop_applyBuiltinNameSuccess typedTakeByteString (BSL.take . fromIntegral)
    $ genTypedBuiltinDef

test_typedDropByteStringSuccess :: TestTree
test_typedDropByteStringSuccess
    = testProperty "typedDropByteString"
    $ prop_applyBuiltinNameSuccess typedDropByteString (BSL.drop . fromIntegral)
    $ genTypedBuiltinDef

test_typedEqByteStringSuccess :: TestTree
test_typedEqByteStringSuccess
    = testProperty "typedEqByteString"
    $ prop_applyBuiltinNameSuccess typedEqByteString (==)
    $ genTypedBuiltinDef
