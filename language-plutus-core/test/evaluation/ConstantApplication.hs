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

import           GHC.Stack
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
    -> (forall b. Size -> TypedBuiltinSized b -> ConstAppProperty b)
    -> Property
prop_typedBuiltinName getFinal (TypedBuiltinName name schema) op allTbs = result where
    result = property . hoist (flip runReaderT $ AllTypedBuiltinSized allTbs) $ do
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

prop_typedBuiltinNameSuccess
    :: TypedBuiltinName a
    -> a
    -> (forall b. Size -> TypedBuiltinSized b -> ConstAppProperty b)
    -> Property
prop_typedBuiltinNameSuccess =
    prop_typedBuiltinName $ \builtin y ->
        ConstAppSuccess <$> typedBuiltinAsValue builtin y

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

test_typedAddIntegerSuccess :: TestTree
test_typedAddIntegerSuccess =
    testProperty "typedAddInteger" $
        prop_typedBuiltinNameSuccess typedAddInteger (+) allTypedBuiltinSizedIntSum

test_typedSubtractIntegerSuccess :: TestTree
test_typedSubtractIntegerSuccess =
    testProperty "typedSubtractInteger" $
        prop_typedBuiltinNameSuccess typedSubtractInteger (-) allTypedBuiltinSizedIntSum

test_typedMultiplyIntegerSuccess :: TestTree
test_typedMultiplyIntegerSuccess =
    testProperty "typedMultiplyInteger" $
        prop_typedBuiltinNameSuccess typedMultiplyInteger (*) $
            allTypedBuiltinSizedInt $ \low high ->
                Range.linear (negate . isqrt . abs $ low) (isqrt high)

test_typedDivideIntegerSuccess :: TestTree
test_typedDivideIntegerSuccess =
    testProperty "typedDivideInteger" $
        prop_typedBuiltinNameSuccess typedDivideInteger div allTypedBuiltinSizedIntDef

test_typedRemainderIntegerSuccess :: TestTree
test_typedRemainderIntegerSuccess =
    testProperty "typedRemainderInteger" $
        prop_typedBuiltinNameSuccess typedRemainderInteger mod allTypedBuiltinSizedIntDef

test_typedLessThanIntegerSuccess :: TestTree
test_typedLessThanIntegerSuccess =
    testProperty "typedLessThanInteger" $
        prop_typedBuiltinNameSuccess typedLessThanInteger (<) allTypedBuiltinSizedIntDef

test_typedLessThanEqIntegerSuccess :: TestTree
test_typedLessThanEqIntegerSuccess =
    testProperty "typedLessThanEqInteger" $
        prop_typedBuiltinNameSuccess typedLessThanEqInteger (<=) allTypedBuiltinSizedIntDef

test_typedGreaterThanIntegerSuccess :: TestTree
test_typedGreaterThanIntegerSuccess =
    testProperty "typedGreaterThanInteger" $
        prop_typedBuiltinNameSuccess typedGreaterThanInteger (>) allTypedBuiltinSizedIntDef

test_typedGreaterThanEqIntegerSuccess :: TestTree
test_typedGreaterThanEqIntegerSuccess =
    testProperty "typedGreaterThanEqInteger" $
        prop_typedBuiltinNameSuccess typedGreaterThanEqInteger (>=) allTypedBuiltinSizedIntDef

test_typedEqIntegerSuccess :: TestTree
test_typedEqIntegerSuccess =
    testProperty "typedEqInteger" $
        prop_typedBuiltinNameSuccess typedEqInteger (==) allTypedBuiltinSizedIntDef

-- test_typedResizeIntegerAny :: TestTree
-- test_typedResizeIntegerAny =
--     testProperty "typedResizeInteger" $
--         prop_typedBuiltinNameAny typedResizeInteger (const id) allTypedBuiltinSizedIntDef

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
