module Evaluation.Constant.Success
    ( test_applyBuiltinNameSuccess
    ) where

import           Language.PlutusCore.Constant
import           Evaluation.Constant.AllTypedBuiltinSized
import           Evaluation.Constant.Apply

import qualified Data.ByteString.Lazy as BSL
import qualified Hedgehog.Range as Range
import           Test.Tasty
import           Test.Tasty.Hedgehog

test_applyBuiltinNameSuccess :: TestTree
test_applyBuiltinNameSuccess =
    -- TODO: fix the divide-by-zero error.
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
        ]

test_typedAddIntegerSuccess :: TestTree
test_typedAddIntegerSuccess
    = testProperty "typedAddInteger"
    $ prop_applyBuiltinNameSuccess typedAddInteger (+)
    $ allTypedBuiltinSizedIntSum

test_typedSubtractIntegerSuccess :: TestTree
test_typedSubtractIntegerSuccess
    = testProperty "typedSubtractInteger"
    $ prop_applyBuiltinNameSuccess typedSubtractInteger (-)
    $ allTypedBuiltinSizedIntSum

test_typedMultiplyIntegerSuccess :: TestTree
test_typedMultiplyIntegerSuccess
    = testProperty "typedMultiplyInteger"
    $ prop_applyBuiltinNameSuccess typedMultiplyInteger (*)
    $ updateAllTypedBuiltinSized
          TypedBuiltinSizedInt
          (\low high -> Range.linear (negate . isqrt . abs $ low) (isqrt high))
    $ allTypedBuiltinSizedDef

test_typedDivideIntegerSuccess :: TestTree
test_typedDivideIntegerSuccess
    = testProperty "typedDivideInteger"
    $ prop_applyBuiltinNameSuccess typedDivideInteger div
    $ allTypedBuiltinSizedDef

test_typedRemainderIntegerSuccess :: TestTree
test_typedRemainderIntegerSuccess
    = testProperty "typedRemainderInteger"
    $ prop_applyBuiltinNameSuccess typedRemainderInteger mod
    $ allTypedBuiltinSizedDef

test_typedLessThanIntegerSuccess :: TestTree
test_typedLessThanIntegerSuccess
    = testProperty "typedLessThanInteger"
    $ prop_applyBuiltinNameSuccess typedLessThanInteger (<)
    $ allTypedBuiltinSizedDef

test_typedLessThanEqIntegerSuccess :: TestTree
test_typedLessThanEqIntegerSuccess
    = testProperty "typedLessThanEqInteger"
    $ prop_applyBuiltinNameSuccess typedLessThanEqInteger (<=)
    $ allTypedBuiltinSizedDef

test_typedGreaterThanIntegerSuccess :: TestTree
test_typedGreaterThanIntegerSuccess
    = testProperty "typedGreaterThanInteger"
    $ prop_applyBuiltinNameSuccess typedGreaterThanInteger (>)
    $ allTypedBuiltinSizedDef

test_typedGreaterThanEqIntegerSuccess :: TestTree
test_typedGreaterThanEqIntegerSuccess
    = testProperty "typedGreaterThanEqInteger"
    $ prop_applyBuiltinNameSuccess typedGreaterThanEqInteger (>=)
    $ allTypedBuiltinSizedDef

test_typedEqIntegerSuccess :: TestTree
test_typedEqIntegerSuccess
    = testProperty "typedEqInteger"
    $ prop_applyBuiltinNameSuccess typedEqInteger (==)
    $ allTypedBuiltinSizedDef

{-
    , typedConcatenate
    , typedTakeByteString
    , typedDropByteString
    , typedEqByteString
-}

isqrt :: Integer -> Integer
isqrt n
    | n < 0     = error "isqrt: negative number"
    | n <= 1    = n
    | otherwise = head $ dropWhile (not . isRoot) iters
    where
        sqr :: Integer -> Integer
        sqr = (^ (2 :: Int))
        twopows = iterate sqr 2
        (lowerRoot, lowerN) = last. takeWhile ((n >=) . snd) $ zip (1 : twopows) twopows
        newtonStep x = div (x + n `div` x) 2
        iters = iterate newtonStep (isqrt (n `div` lowerN) * lowerRoot)
        isRoot r = sqr r <= n && n < sqr (r+1)
