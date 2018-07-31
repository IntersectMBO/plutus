-- | See the 'docs/Constant application.md' article for how this module emerged.

{-# LANGUAGE GADTs #-}
module Language.PlutusCore.Constant.Typed
    ( SizeVar(..)
    , BuiltinSized(..)
    , TypedBuiltinSized(..)
    , TypedBuiltin(..)
    , TypeScheme(..)
    , TypedBuiltinName(..)
    , eraseTypedBuiltinSized
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
    , typedResizeInteger
    , typedIntToByteString
    ) where

import           PlutusPrelude
import           Language.PlutusCore.Lexer.Type (BuiltinName(..))
import           Language.PlutusCore.Constant.Prelude

import qualified Data.ByteString.Lazy as BSL

infixr 9 `TypeSchemeArrow`

newtype SizeVar = SizeVar Int

-- | Built-in types indexed by @size@.
data BuiltinSized
    = BuiltinSizedInt
    | BuiltinSizedBS
    | BuiltinSizedSize
    deriving (Show, Eq)

-- | Built-in types indexed by @size@ along with their denotation.
data TypedBuiltinSized a where
    TypedBuiltinSizedInt  :: TypedBuiltinSized Integer
    TypedBuiltinSizedBS   :: TypedBuiltinSized BSL.ByteString
    TypedBuiltinSizedSize :: TypedBuiltinSized Size

-- | Built-in types. A type is considired "built-in" if it can appear in the type signature
-- of a primitive operation. So @boolean@ is considered built-in even though it is defined in PLC
-- and is not primitive.
data TypedBuiltin a where
    TypedBuiltinSized :: SizeVar -> TypedBuiltinSized a -> TypedBuiltin a
    TypedBuiltinBool  :: TypedBuiltin Bool

-- | Type schemes of primitive operations.
data TypeScheme a where
    TypeSchemeBuiltin :: TypedBuiltin a -> TypeScheme a
    TypeSchemeArrow   :: TypeScheme a -> TypeScheme b -> TypeScheme (a -> b)
    TypeSchemeForall  :: (SizeVar -> TypeScheme a) -> TypeScheme a

-- | A 'BuiltinName' with an associated 'TypeScheme'.
data TypedBuiltinName a = TypedBuiltinName
    { _typedBuiltinNameUntyped    :: BuiltinName
    , _typedBuiltinNameTypeScheme :: TypeScheme a
    }

instance Enum SizeVar where
    toEnum = SizeVar
    fromEnum (SizeVar sizeIndex) = sizeIndex

instance Pretty BuiltinSized where
    pretty = undefined

instance Pretty (TypedBuiltinSized a) where
    pretty = undefined

instance Pretty (TypedBuiltin a) where
    pretty = undefined

eraseTypedBuiltinSized :: TypedBuiltinSized a -> BuiltinSized
eraseTypedBuiltinSized TypedBuiltinSizedInt  = BuiltinSizedInt
eraseTypedBuiltinSized TypedBuiltinSizedBS   = BuiltinSizedBS
eraseTypedBuiltinSized TypedBuiltinSizedSize = BuiltinSizedSize

sizeIntIntInt :: TypeScheme (Integer -> Integer -> Integer)
sizeIntIntInt =
    TypeSchemeForall $ \s ->
        TypeSchemeBuiltin (TypedBuiltinSized s TypedBuiltinSizedInt) `TypeSchemeArrow`
        TypeSchemeBuiltin (TypedBuiltinSized s TypedBuiltinSizedInt) `TypeSchemeArrow`
        TypeSchemeBuiltin (TypedBuiltinSized s TypedBuiltinSizedInt)

sizeIntIntBool :: TypeScheme (Integer -> Integer -> Bool)
sizeIntIntBool =
    TypeSchemeForall $ \s ->
        TypeSchemeBuiltin (TypedBuiltinSized s TypedBuiltinSizedInt) `TypeSchemeArrow`
        TypeSchemeBuiltin (TypedBuiltinSized s TypedBuiltinSizedInt) `TypeSchemeArrow`
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

typedResizeInteger :: TypedBuiltinName (Natural -> Integer -> Integer)
typedResizeInteger =
    TypedBuiltinName ResizeInteger $
        TypeSchemeForall $ \s0 -> TypeSchemeForall $ \s1 ->
            TypeSchemeBuiltin (TypedBuiltinSized s1 TypedBuiltinSizedSize) `TypeSchemeArrow`
            TypeSchemeBuiltin (TypedBuiltinSized s0 TypedBuiltinSizedInt) `TypeSchemeArrow`
            TypeSchemeBuiltin (TypedBuiltinSized s1 TypedBuiltinSizedInt)

typedIntToByteString :: TypedBuiltinName (Natural -> Integer -> BSL.ByteString)
typedIntToByteString =
    TypedBuiltinName IntToByteString $
        TypeSchemeForall $ \s0 -> TypeSchemeForall $ \s1 ->
            TypeSchemeBuiltin (TypedBuiltinSized s1 TypedBuiltinSizedSize) `TypeSchemeArrow`
            TypeSchemeBuiltin (TypedBuiltinSized s0 TypedBuiltinSizedInt) `TypeSchemeArrow`
            TypeSchemeBuiltin (TypedBuiltinSized s1 TypedBuiltinSizedBS)
