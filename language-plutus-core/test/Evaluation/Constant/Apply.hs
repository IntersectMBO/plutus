{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTs      #-}
module Evaluation.Constant.Apply where

import           Language.PlutusCore
import           Language.PlutusCore.Constant
import           Evaluation.Constant.AllTypedBuiltinSized

import           GHC.Stack
import           Control.Monad.Reader
import           Control.Monad.Morph
import           Hedgehog hiding (Size, Var, annotate)
import qualified Hedgehog.Gen   as Gen
import qualified Hedgehog.Range as Range

type ConstAppProperty = PropertyT (ReaderT TheAllTypedBuiltinSized IO)

evalMaybe :: (MonadTest m, Show e, HasCallStack) => e -> Maybe a -> m a
evalMaybe e = evalEither . maybe (Left e) Right

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

prop_applyBuiltinName
    :: (forall b. TypedBuiltin Size b -> b -> ConstAppProperty ConstAppResult)
    -> TypedBuiltinName a
    -> a
    -> AllTypedBuiltinSized
    -> Property
prop_applyBuiltinName getFinal (TypedBuiltinName name schema) op allTbs = result where
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

prop_applyBuiltinNameSuccess :: TypedBuiltinName a -> a -> AllTypedBuiltinSized -> Property
prop_applyBuiltinNameSuccess =
    prop_applyBuiltinName $ \tbs -> fmap ConstAppSuccess . typedBuiltinAsValue tbs

prop_applyBuiltinNameSuccessFailure :: TypedBuiltinName a -> a -> Property
prop_applyBuiltinNameSuccessFailure tbn x =
    prop_applyBuiltinName (\tbs -> return . makeConstantApp tbs) tbn x allTypedBuiltinSizedDef
