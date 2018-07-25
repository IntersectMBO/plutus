{-# LANGUAGE GADTs #-}
module Language.PlutusCore.Constant.Typed
    ( SizeVar(..)
    , TypedBuiltinSized(..)
    , TypedBuiltin(..)
    , TypeSchema(..)
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
    ) where

import           PlutusPrelude
import           Language.PlutusCore.Lexer.Type (BuiltinName(..))
import           Language.PlutusCore.Constant.Prelude

import qualified Data.ByteString.Lazy as BSL

infixr 9 `TypeSchemaArrow`

newtype SizeVar = SizeVar Int

instance Enum SizeVar where
    toEnum = SizeVar
    fromEnum (SizeVar sizeIndex) = sizeIndex

data TypedBuiltinSized a where
    TypedBuiltinInt  :: TypedBuiltinSized Integer
    TypedBuiltinBS   :: TypedBuiltinSized BSL.ByteString
    TypedBuiltinSize :: TypedBuiltinSized Size

data TypedBuiltin a where
    TypedBuiltinSized :: SizeVar -> TypedBuiltinSized a -> TypedBuiltin a
    TypedBuiltinBool  :: TypedBuiltin Bool

data TypeSchema a where
    TypeSchemaBuiltin :: TypedBuiltin a -> TypeSchema a
    TypeSchemaArrow   :: TypeSchema a -> TypeSchema b -> TypeSchema (a -> b)
    TypeSchemaForall  :: (SizeVar -> TypeSchema a) -> TypeSchema a

data TypedBuiltinName a = TypedBuiltinName BuiltinName (TypeSchema a)

instance Pretty (TypedBuiltinSized a) where
    pretty = undefined

instance Pretty (TypedBuiltin a) where
    pretty = undefined

sizeIntIntInt :: TypeSchema (Integer -> Integer -> Integer)
sizeIntIntInt =
    TypeSchemaForall $ \s ->
        TypeSchemaBuiltin (TypedBuiltinSized s TypedBuiltinInt) `TypeSchemaArrow`
        TypeSchemaBuiltin (TypedBuiltinSized s TypedBuiltinInt) `TypeSchemaArrow`
        TypeSchemaBuiltin (TypedBuiltinSized s TypedBuiltinInt)

sizeIntIntBool :: TypeSchema (Integer -> Integer -> Bool)
sizeIntIntBool =
    TypeSchemaForall $ \s ->
        TypeSchemaBuiltin (TypedBuiltinSized s TypedBuiltinInt) `TypeSchemaArrow`
        TypeSchemaBuiltin (TypedBuiltinSized s TypedBuiltinInt) `TypeSchemaArrow`
        TypeSchemaBuiltin TypedBuiltinBool

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
