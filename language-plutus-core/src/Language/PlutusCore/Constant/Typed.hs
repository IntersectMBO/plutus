{-# LANGUAGE GADTs #-}
module Language.PlutusCore.Constant.Typed
    ( SizeVar(..)
    , TypedBuiltinSized(..)
    , TypedBuiltin(..)
    , TypeScheme(..)
    , TypedBuiltinName(..)
    , typedAddInteger
    , typedSubtractInteger
    , typedMultiplyInteger
    , typedDivideInteger
    , typedRemainderInteger
    , typedLessThanInteger
    , typedLessThanEqInteger
    , typedGreaterThanInteger
    , typedGreaterThanEqInteger
    , typedEqInteger
    -- , typedResizeInteger
    , typedIntToByteString
    ) where

import           PlutusPrelude
import           Language.PlutusCore.Lexer.Type (BuiltinName(..))
import           Language.PlutusCore.Constant.Prelude

import qualified Data.ByteString.Lazy as BSL

infixr 9 `TypeSchemeArrow`

newtype SizeVar = SizeVar Int

data TypedBuiltinSized a where
    TypedBuiltinInt  :: TypedBuiltinSized Integer
    TypedBuiltinBS   :: TypedBuiltinSized BSL.ByteString
    TypedBuiltinSize :: TypedBuiltinSized Size

data TypedBuiltin a where
    TypedBuiltinSized :: SizeVar -> TypedBuiltinSized a -> TypedBuiltin a
    TypedBuiltinBool  :: TypedBuiltin Bool

data TypeScheme a where
    TypeSchemeBuiltin :: TypedBuiltin a -> TypeScheme a
    TypeSchemeArrow   :: TypeScheme a -> TypeScheme b -> TypeScheme (a -> b)
    TypeSchemeForall  :: (SizeVar -> TypeScheme a) -> TypeScheme a

data TypedBuiltinName a = TypedBuiltinName BuiltinName (TypeScheme a)

instance Enum SizeVar where
    toEnum = SizeVar
    fromEnum (SizeVar sizeIndex) = sizeIndex

instance Pretty (TypedBuiltinSized a) where
    pretty = undefined

instance Pretty (TypedBuiltin a) where
    pretty = undefined

sizeIntIntInt :: TypeScheme (Integer -> Integer -> Integer)
sizeIntIntInt =
    TypeSchemeForall $ \s ->
        TypeSchemeBuiltin (TypedBuiltinSized s TypedBuiltinInt) `TypeSchemeArrow`
        TypeSchemeBuiltin (TypedBuiltinSized s TypedBuiltinInt) `TypeSchemeArrow`
        TypeSchemeBuiltin (TypedBuiltinSized s TypedBuiltinInt)

sizeIntIntBool :: TypeScheme (Integer -> Integer -> Bool)
sizeIntIntBool =
    TypeSchemeForall $ \s ->
        TypeSchemeBuiltin (TypedBuiltinSized s TypedBuiltinInt) `TypeSchemeArrow`
        TypeSchemeBuiltin (TypedBuiltinSized s TypedBuiltinInt) `TypeSchemeArrow`
        TypeSchemeBuiltin TypedBuiltinBool

typedAddInteger :: TypedBuiltinName (Integer -> Integer -> Integer)
typedAddInteger = TypedBuiltinName AddInteger sizeIntIntInt

typedSubtractInteger :: TypedBuiltinName (Integer -> Integer -> Integer)
typedSubtractInteger = TypedBuiltinName SubtractInteger sizeIntIntInt

typedMultiplyInteger :: TypedBuiltinName (Integer -> Integer -> Integer)
typedMultiplyInteger = TypedBuiltinName MultiplyInteger sizeIntIntInt

typedDivideInteger :: TypedBuiltinName (Integer -> Integer -> Integer)
typedDivideInteger = TypedBuiltinName DivideInteger sizeIntIntInt

typedRemainderInteger :: TypedBuiltinName (Integer -> Integer -> Integer)
typedRemainderInteger = TypedBuiltinName RemainderInteger sizeIntIntInt

typedLessThanInteger :: TypedBuiltinName (Integer -> Integer -> Bool)
typedLessThanInteger = TypedBuiltinName LessThanInteger sizeIntIntBool

typedLessThanEqInteger :: TypedBuiltinName (Integer -> Integer -> Bool)
typedLessThanEqInteger = TypedBuiltinName LessThanEqInteger sizeIntIntBool

typedGreaterThanInteger :: TypedBuiltinName (Integer -> Integer -> Bool)
typedGreaterThanInteger = TypedBuiltinName GreaterThanInteger sizeIntIntBool

typedGreaterThanEqInteger :: TypedBuiltinName (Integer -> Integer -> Bool)
typedGreaterThanEqInteger = TypedBuiltinName GreaterThanEqInteger sizeIntIntBool

typedEqInteger :: TypedBuiltinName (Integer -> Integer -> Bool)
typedEqInteger = TypedBuiltinName EqInteger sizeIntIntBool

-- typedResizeInteger :: TypedBuiltinName (Natural -> Integer -> Integer)
-- typedResizeInteger =
--     TypedBuiltinName ResizeInteger $
--         TypeSchemeForall $ \s0 -> TypeSchemeForall $ \s1 ->
--             TypeSchemeBuiltin (TypedBuiltinSized s1 TypedBuiltinSize) `TypeSchemeArrow`
--             TypeSchemeBuiltin (TypedBuiltinSized s0 TypedBuiltinInt) `TypeSchemeArrow`
--             TypeSchemeBuiltin (TypedBuiltinSized s1 TypedBuiltinInt)

typedIntToByteString :: TypedBuiltinName (Natural -> Integer -> BSL.ByteString)
typedIntToByteString =
    TypedBuiltinName IntToByteString $
        TypeSchemeForall $ \s0 -> TypeSchemeForall $ \s1 ->
            TypeSchemeBuiltin (TypedBuiltinSized s1 TypedBuiltinSize) `TypeSchemeArrow`
            TypeSchemeBuiltin (TypedBuiltinSized s0 TypedBuiltinInt) `TypeSchemeArrow`
            TypeSchemeBuiltin (TypedBuiltinSized s1 TypedBuiltinBS)
