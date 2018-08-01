{-# LANGUAGE GADTs #-}
module ConstantApplication where

import           Language.PlutusCore
-- TODO: export a single 'Language.PlutusCore.Constant'
import           Language.PlutusCore.Constant.Prelude
import           Language.PlutusCore.Constant.Make
import           Language.PlutusCore.Constant.Typed
import           Language.PlutusCore.Constant.Apply

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
       -- , test_typedMultiplyInteger
       -- , test_typedDivideInteger
       -- , test_typedRemainderInteger
       -- , test_typedLessThanInteger
       -- , test_typedLessThanEqInteger
       -- , test_typedGreaterThanInteger
       -- , test_typedGreaterThanEqInteger
       -- , test_typedEqInteger
       -- , test_typedResizeInteger
       ]

allTypedBuiltinSized :: Size -> TypedBuiltinSized a -> PropertyT IO a
allTypedBuiltinSized size TypedBuiltinSizedInt  =
    -- TODO: this works only for addition, fix it.
    let (low, high) = toBoundsInt size in
        forAll . Gen.integral $ Range.linear (low `div` 2) ((high - 1) `div` 2)
allTypedBuiltinSized size TypedBuiltinSizedBS   = undefined
allTypedBuiltinSized size TypedBuiltinSizedSize = undefined

allTypedBuiltin :: TypedBuiltin Size a -> PropertyT IO a
allTypedBuiltin (TypedBuiltinSized size tbs) = allTypedBuiltinSized size tbs
allTypedBuiltin TypedBuiltinBool             = forAll Gen.bool

typedBuiltinAsValue :: TypedBuiltin Size a -> a -> PropertyT IO (Value TyName Name ())
typedBuiltinAsValue builtin
    = evalEither
    . maybe (Left "prop_typedAddInteger: out of bounds") Right
    . makeConstant builtin

getTypedBuiltinAndItsValue :: TypedBuiltin Size a -> PropertyT IO (a, Value TyName Name ())
getTypedBuiltinAndItsValue builtin = do
    x <- allTypedBuiltin builtin
    v <- typedBuiltinAsValue builtin x
    return (x, v)

getSchemedAndItsValue :: TypeScheme Size a -> PropertyT IO (a, Value TyName Name ())
getSchemedAndItsValue (TypeSchemeBuiltin builtin) = getTypedBuiltinAndItsValue builtin
getSchemedAndItsValue (TypeSchemeArrow schA schB) = undefined
getSchemedAndItsValue (TypeSchemeAllSize schK)    = undefined

prop_typedBuiltinName :: TypedBuiltinName a -> a -> Property
prop_typedBuiltinName (TypedBuiltinName name schema) = result where
    result op = property $ do
        size <- forAll . Gen.integral $ Range.linear 1 4
        go (\args res -> applyBuiltinName name args === ConstAppSuccess res) size schema op

    go
        :: ([Value TyName Name ()] -> Value TyName Name () -> PropertyT IO ())
        -> Size -> TypeScheme Size a -> a -> PropertyT IO ()
    go ret _    (TypeSchemeBuiltin builtin) y = do
        w <- typedBuiltinAsValue builtin y
        ret [] w
    go ret size (TypeSchemeArrow schA schB) f = do
        (x, v) <- getSchemedAndItsValue schA
        go (ret . (v :)) size schB (f x)
    go ret size (TypeSchemeAllSize schK)    f =
        go ret size (schK size) f

test_typedAddInteger :: TestTree
test_typedAddInteger =
    testProperty "typedAddInteger" $
        prop_typedBuiltinName typedAddInteger (+)

test_typedSubtractInteger :: TestTree
test_typedSubtractInteger =
    testProperty "typedSubtractInteger" $
        prop_typedBuiltinName typedSubtractInteger (-)

test_typedMultiplyInteger :: TestTree
test_typedMultiplyInteger =
    testProperty "typedMultiplyInteger" $
        prop_typedBuiltinName typedMultiplyInteger (*)

test_typedDivideInteger :: TestTree
test_typedDivideInteger =
    testProperty "typedDivideInteger" $
        prop_typedBuiltinName typedDivideInteger div

test_typedRemainderInteger :: TestTree
test_typedRemainderInteger =
    testProperty "typedRemainderInteger" $
        prop_typedBuiltinName typedRemainderInteger mod

test_typedLessThanInteger :: TestTree
test_typedLessThanInteger =
    testProperty "typedLessThanInteger" $
        prop_typedBuiltinName typedLessThanInteger (<)

test_typedLessThanEqInteger :: TestTree
test_typedLessThanEqInteger =
    testProperty "typedLessThanEqInteger" $
        prop_typedBuiltinName typedLessThanEqInteger (<=)

test_typedGreaterThanInteger :: TestTree
test_typedGreaterThanInteger =
    testProperty "typedGreaterThanInteger" $
        prop_typedBuiltinName typedGreaterThanInteger (>)

test_typedGreaterThanEqInteger :: TestTree
test_typedGreaterThanEqInteger =
    testProperty "typedGreaterThanEqInteger" $
        prop_typedBuiltinName typedGreaterThanEqInteger (>=)

test_typedEqInteger :: TestTree
test_typedEqInteger =
    testProperty "typedEqInteger" $
        prop_typedBuiltinName typedEqInteger (==)

test_typedResizeInteger :: TestTree
test_typedResizeInteger =
    testProperty "typedResizeInteger" $
        prop_typedBuiltinName typedResizeInteger (const id)
