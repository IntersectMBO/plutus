{-# LANGUAGE RankNTypes       #-}
{-# LANGUAGE GADTs            #-}
{-# LANGUAGE TypeApplications #-}
module ConstantApplication where

import           Language.PlutusCore
-- TODO: export a single 'Language.PlutusCore.Constant'
import           Language.PlutusCore.Constant.Prelude
import           Language.PlutusCore.Constant.Make
import           Language.PlutusCore.Constant.Typed
import           Language.PlutusCore.Constant.Apply

import           Control.Monad.Reader
import           Control.Monad.Morph
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
    testGroup "typedBuiltinName"
       [ test_typedAddInteger
       , test_typedSubtractInteger
       , test_typedMultiplyInteger
       , test_typedDivideInteger
       , test_typedRemainderInteger
       , test_typedLessThanInteger
       , test_typedLessThanEqInteger
       , test_typedGreaterThanInteger
       , test_typedGreaterThanEqInteger
       , test_typedEqInteger
       -- TODO: that's not gonna work.
       -- , test_typedResizeInteger
       ]

type ConstAppProperty = PropertyT (ReaderT AllTypedBuiltinSized IO)

newtype AllTypedBuiltinSized = AllTypedBuiltinSized
    { unAlltypedBuilinSized :: forall a. Size -> TypedBuiltinSized a -> ConstAppProperty a
    }

allTypedBuiltin :: TypedBuiltin Size a -> ConstAppProperty a
allTypedBuiltin (TypedBuiltinSized size tbs) = do
    AllTypedBuiltinSized allTbs <- ask
    allTbs size tbs
allTypedBuiltin TypedBuiltinBool             = forAll Gen.bool

typedBuiltinAsValue :: TypedBuiltin Size a -> a -> ConstAppProperty (Value TyName Name ())
typedBuiltinAsValue builtin
    = evalEither
    -- TODO: improve the error message.
    . maybe (Left "prop_typedAddInteger: out of bounds") Right
    . makeConstant builtin

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
    :: TypedBuiltinName a
    -> a
    -> (forall b. Size -> TypedBuiltinSized b -> ConstAppProperty b)
    -> Property
prop_typedBuiltinName (TypedBuiltinName name schema) op allTbs = result where
    result = property . hoist (flip runReaderT $ AllTypedBuiltinSized allTbs) $ do
        size <- forAll . Gen.integral $ Range.exponential 1 128
        go (applyBuiltinName name) size schema op

    go
        :: ([Value TyName Name ()] -> ConstAppResult)
        -> Size -> TypeScheme Size a -> a -> ConstAppProperty ()
    go app _    (TypeSchemeBuiltin builtin) y = do
        w <- typedBuiltinAsValue builtin y
        app [] === ConstAppSuccess w
    go app size (TypeSchemeArrow schA schB) f = do
        (x, v) <- getSchemedAndItsValue schA
        go (app . (v :)) size schB (f x)
    go app size (TypeSchemeAllSize schK)    f =
        go app size (schK size) f

allTypedBuiltinSizedDef :: Size -> TypedBuiltinSized a -> ConstAppProperty a
allTypedBuiltinSizedDef _ tbs = fail $ concat
    [ "The generator for the following builtin is not implemented: "
    , show $ eraseTypedBuiltinSized tbs
    ]

allTypedBuiltinSizedInt
    :: (Integer -> Integer -> Range Integer) -> Size -> TypedBuiltinSized a -> ConstAppProperty a
allTypedBuiltinSizedInt toRange size TypedBuiltinSizedInt =
    let (low, high) = toBoundsInt size in
        forAll . Gen.integral $ toRange low (high - 1)
allTypedBuiltinSizedInt _       size tbs                  =
    allTypedBuiltinSizedDef size tbs

allTypedBuiltinSizedIntDef :: Size -> TypedBuiltinSized a -> ConstAppProperty a
allTypedBuiltinSizedIntDef = allTypedBuiltinSizedInt Range.linear

allTypedBuiltinSizedIntSum :: Size -> TypedBuiltinSized a -> ConstAppProperty a
allTypedBuiltinSizedIntSum =
    allTypedBuiltinSizedInt $ \low high ->
        Range.linear (low `div` 2) (high `div` 2)

test_typedAddInteger :: TestTree
test_typedAddInteger =
    testProperty "typedAddInteger" $
        prop_typedBuiltinName typedAddInteger (+) allTypedBuiltinSizedIntSum

test_typedSubtractInteger :: TestTree
test_typedSubtractInteger =
    testProperty "typedSubtractInteger" $
        prop_typedBuiltinName typedSubtractInteger (-) allTypedBuiltinSizedIntSum

test_typedMultiplyInteger :: TestTree
test_typedMultiplyInteger =
    testProperty "typedMultiplyInteger" $
        prop_typedBuiltinName typedMultiplyInteger (*) $
            allTypedBuiltinSizedInt $ \low high ->
                Range.linear (negate . isqrt . abs $ low) (isqrt high)

test_typedDivideInteger :: TestTree
test_typedDivideInteger =
    testProperty "typedDivideInteger" $
        prop_typedBuiltinName typedDivideInteger div allTypedBuiltinSizedIntDef

test_typedRemainderInteger :: TestTree
test_typedRemainderInteger =
    testProperty "typedRemainderInteger" $
        prop_typedBuiltinName typedRemainderInteger mod allTypedBuiltinSizedIntDef

test_typedLessThanInteger :: TestTree
test_typedLessThanInteger =
    testProperty "typedLessThanInteger" $
        prop_typedBuiltinName typedLessThanInteger (<) allTypedBuiltinSizedIntDef

test_typedLessThanEqInteger :: TestTree
test_typedLessThanEqInteger =
    testProperty "typedLessThanEqInteger" $
        prop_typedBuiltinName typedLessThanEqInteger (<=) allTypedBuiltinSizedIntDef

test_typedGreaterThanInteger :: TestTree
test_typedGreaterThanInteger =
    testProperty "typedGreaterThanInteger" $
        prop_typedBuiltinName typedGreaterThanInteger (>) allTypedBuiltinSizedIntDef

test_typedGreaterThanEqInteger :: TestTree
test_typedGreaterThanEqInteger =
    testProperty "typedGreaterThanEqInteger" $
        prop_typedBuiltinName typedGreaterThanEqInteger (>=) allTypedBuiltinSizedIntDef

test_typedEqInteger :: TestTree
test_typedEqInteger =
    testProperty "typedEqInteger" $
        prop_typedBuiltinName typedEqInteger (==) allTypedBuiltinSizedIntDef

test_typedResizeInteger :: TestTree
test_typedResizeInteger =
    testProperty "typedResizeInteger" $
        prop_typedBuiltinName typedResizeInteger (const id) allTypedBuiltinSizedIntDef

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
