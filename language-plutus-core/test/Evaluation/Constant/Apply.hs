{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTs      #-}
module Evaluation.Constant.Apply where

import           Language.PlutusCore
import           Language.PlutusCore.Constant
import           Evaluation.Constant.AllTypedBuiltinSized

import           GHC.Stack
import           Control.Monad.Reader
import           Control.Monad.Morph
import qualified Data.ByteString.Lazy as BSL
import           Hedgehog hiding (Size, Var, annotate)
import qualified Hedgehog.Gen   as Gen
import qualified Hedgehog.Range as Range
import           Test.Tasty
import           Test.Tasty.Hedgehog

main :: IO ()
main = defaultMain tests_ConstantApplication

tests_ConstantApplication :: TestTree
tests_ConstantApplication =
    testGroup "constantApplication"
        [ tests_typedBuiltinName
        ]

tests_typedBuiltinName :: TestTree
tests_typedBuiltinName =
    -- TODO: fix the divide-by-zero error.
    testGroup "typedBuiltinName"
       [ testGroup "Success"
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
       , testGroup "Any"
           [ test_typedAddIntegerAny
           , test_typedSubtractIntegerAny
           , test_typedMultiplyIntegerAny
           , test_typedDivideIntegerAny
           , test_typedRemainderIntegerAny
           , test_typedLessThanIntegerAny
           , test_typedLessThanEqIntegerAny
           , test_typedGreaterThanIntegerAny
           , test_typedGreaterThanEqIntegerAny
           , test_typedEqIntegerAny
           , test_typedResizeIntegerAny
           ]
       ]
type ConstAppProperty = PropertyT (ReaderT TheAllTypedBuiltinSized IO)

allTypedBuiltin :: TypedBuiltin Size a -> ConstAppProperty a
allTypedBuiltin (TypedBuiltinSized sizeEntry tbs) = do
    TheAllTypedBuiltinSized allTbs <- ask
    allTbs (flattenSizeEntry sizeEntry) tbs
allTypedBuiltin TypedBuiltinBool                  = forAll Gen.bool

typedBuiltinAsValue :: TypedBuiltin Size a -> a -> ConstAppProperty (Value TyName Name ())
typedBuiltinAsValue builtin x = evalMaybe err $ makeConstant builtin x where
    err = "prop_typedAddInteger: out of bounds: " ++ prettyTypedBuiltinString builtin x

getTypedBuiltinAndItsValue :: TypedBuiltin Size a -> ConstAppProperty (a, Value TyName Name ())
getTypedBuiltinAndItsValue builtin = do
    x <- allTypedBuiltin builtin
    v <- typedBuiltinAsValue builtin x
    return (x, v)

getSchemedAndItsValue :: TypeScheme Size a -> ConstAppProperty (a, Value TyName Name ())
getSchemedAndItsValue (TypeSchemeBuiltin builtin) = getTypedBuiltinAndItsValue builtin
getSchemedAndItsValue (TypeSchemeArrow _ _)       = undefined
getSchemedAndItsValue (TypeSchemeAllSize _)       = undefined

prop_typedBuiltinName
    :: (forall b. TypedBuiltin Size b -> b -> ConstAppProperty ConstAppResult)
    -> TypedBuiltinName a
    -> a
    -> AllTypedBuiltinSized
    -> Property
prop_typedBuiltinName getFinal (TypedBuiltinName name schema) op allTbs = result where
    result = property . hoist (flip runReaderT $ TheAllTypedBuiltinSized allTbs) $ do
        size <- forAll . Gen.integral $ Range.exponential 1 128
        go (applyBuiltinName name) size schema op

    go
        :: ([Value TyName Name ()] -> ConstAppResult)
        -> Size -> TypeScheme Size a -> a -> ConstAppProperty ()
    go app _    (TypeSchemeBuiltin builtin) y = do
        final <- getFinal builtin y
        app [] === final
    go app size (TypeSchemeArrow schA schB) f = do
        (x, v) <- getSchemedAndItsValue schA
        go (app . (v :)) size schB (f x)
    go app size (TypeSchemeAllSize schK)    f =
        go app size (schK size) f

prop_typedBuiltinNameSuccess :: TypedBuiltinName a -> a -> AllTypedBuiltinSized -> Property
prop_typedBuiltinNameSuccess =
    prop_typedBuiltinName $ \tbs -> fmap ConstAppSuccess . typedBuiltinAsValue tbs

prop_typedBuiltinNameAny :: TypedBuiltinName a -> a -> Property
prop_typedBuiltinNameAny tbn x =
    prop_typedBuiltinName (\tbs -> return . makeConstantApp tbs) tbn x allTypedBuiltinSizedDef

test_typedAddIntegerSuccess :: TestTree
test_typedAddIntegerSuccess
    = testProperty "typedAddInteger"
    $ prop_typedBuiltinNameSuccess typedAddInteger (+)
    $ allTypedBuiltinSizedIntSum

test_typedSubtractIntegerSuccess :: TestTree
test_typedSubtractIntegerSuccess
    = testProperty "typedSubtractInteger"
    $ prop_typedBuiltinNameSuccess typedSubtractInteger (-)
    $ allTypedBuiltinSizedIntSum

test_typedMultiplyIntegerSuccess :: TestTree
test_typedMultiplyIntegerSuccess
    = testProperty "typedMultiplyInteger"
    $ prop_typedBuiltinNameSuccess typedMultiplyInteger (*)
    $ updateAllTypedBuiltinSized
          TypedBuiltinSizedInt
          (\low high -> Range.linear (negate . isqrt . abs $ low) (isqrt high))
    $ allTypedBuiltinSizedDef

test_typedDivideIntegerSuccess :: TestTree
test_typedDivideIntegerSuccess
    = testProperty "typedDivideInteger"
    $ prop_typedBuiltinNameSuccess typedDivideInteger div
    $ allTypedBuiltinSizedDef

test_typedRemainderIntegerSuccess :: TestTree
test_typedRemainderIntegerSuccess
    = testProperty "typedRemainderInteger"
    $ prop_typedBuiltinNameSuccess typedRemainderInteger mod
    $ allTypedBuiltinSizedDef

test_typedLessThanIntegerSuccess :: TestTree
test_typedLessThanIntegerSuccess
    = testProperty "typedLessThanInteger"
    $ prop_typedBuiltinNameSuccess typedLessThanInteger (<)
    $ allTypedBuiltinSizedDef

test_typedLessThanEqIntegerSuccess :: TestTree
test_typedLessThanEqIntegerSuccess
    = testProperty "typedLessThanEqInteger"
    $ prop_typedBuiltinNameSuccess typedLessThanEqInteger (<=)
    $ allTypedBuiltinSizedDef

test_typedGreaterThanIntegerSuccess :: TestTree
test_typedGreaterThanIntegerSuccess
    = testProperty "typedGreaterThanInteger"
    $ prop_typedBuiltinNameSuccess typedGreaterThanInteger (>)
    $ allTypedBuiltinSizedDef

test_typedGreaterThanEqIntegerSuccess :: TestTree
test_typedGreaterThanEqIntegerSuccess
    = testProperty "typedGreaterThanEqInteger"
    $ prop_typedBuiltinNameSuccess typedGreaterThanEqInteger (>=)
    $ allTypedBuiltinSizedDef

test_typedEqIntegerSuccess :: TestTree
test_typedEqIntegerSuccess
    = testProperty "typedEqInteger"
    $ prop_typedBuiltinNameSuccess typedEqInteger (==)
    $ allTypedBuiltinSizedDef

test_typedAddIntegerAny :: TestTree
test_typedAddIntegerAny
    = testProperty "typedAddInteger"
    $ prop_typedBuiltinNameAny typedAddInteger (+)

test_typedSubtractIntegerAny :: TestTree
test_typedSubtractIntegerAny
    = testProperty "typedSubtractInteger"
    $ prop_typedBuiltinNameAny typedSubtractInteger (-)

test_typedMultiplyIntegerAny :: TestTree
test_typedMultiplyIntegerAny
    = testProperty "typedMultiplyInteger"
    $ prop_typedBuiltinNameAny typedMultiplyInteger (*)

test_typedDivideIntegerAny :: TestTree
test_typedDivideIntegerAny
    = testProperty "typedDivideInteger"
    $ prop_typedBuiltinNameAny typedDivideInteger div

test_typedRemainderIntegerAny :: TestTree
test_typedRemainderIntegerAny
    = testProperty "typedRemainderInteger"
    $ prop_typedBuiltinNameAny typedRemainderInteger mod

test_typedLessThanIntegerAny :: TestTree
test_typedLessThanIntegerAny
    = testProperty "typedLessThanInteger"
    $ prop_typedBuiltinNameAny typedLessThanInteger (<)

test_typedLessThanEqIntegerAny :: TestTree
test_typedLessThanEqIntegerAny
    = testProperty "typedLessThanEqInteger"
    $ prop_typedBuiltinNameAny typedLessThanEqInteger (<=)

test_typedGreaterThanIntegerAny :: TestTree
test_typedGreaterThanIntegerAny
    = testProperty "typedGreaterThanInteger"
    $ prop_typedBuiltinNameAny typedGreaterThanInteger (>)

test_typedGreaterThanEqIntegerAny :: TestTree
test_typedGreaterThanEqIntegerAny
    = testProperty "typedGreaterThanEqInteger"
    $ prop_typedBuiltinNameAny typedGreaterThanEqInteger (>=)

test_typedEqIntegerAny :: TestTree
test_typedEqIntegerAny
    = testProperty "typedEqInteger"
    $ prop_typedBuiltinNameAny typedEqInteger (==)

test_typedResizeIntegerAny :: TestTree
test_typedResizeIntegerAny
    = testProperty "typedResizeInteger"
    $ prop_typedBuiltinNameAny typedResizeInteger (const id)

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

evalMaybe :: (MonadTest m, Show e, HasCallStack) => e -> Maybe a -> m a
evalMaybe e = evalEither . maybe (Left e) Right
