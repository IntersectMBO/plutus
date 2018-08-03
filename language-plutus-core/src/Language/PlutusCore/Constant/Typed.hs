-- | See the 'docs/Constant application.md' article for how this module emerged.

{-# LANGUAGE GADTs             #-}
{-# LANGUAGE RankNTypes        #-}
{-# LANGUAGE DeriveFunctor     #-}
{-# LANGUAGE OverloadedStrings #-}
module Language.PlutusCore.Constant.Typed
    ( BuiltinSized(..)
    , TypedBuiltinSized(..)
    , SizeEntry(..)
    , TypedBuiltin(..)
    , TypedBuiltinValue(..)
    , TypeScheme(..)
    , TypedBuiltinName(..)
    , flattenSizeEntry
    , eraseTypedBuiltinSized
    , fmapSizeTypedBuiltin
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
    , typedConcatenate
    , typedTakeByteString
    , typedDropByteString
    , typedSHA2
    , typedSHA3
    , typedVerifySignature
    , typedResizeByteString
    , typedEqByteString
    , typedTxHash
    ) where

import           PlutusPrelude
import           Language.PlutusCore.Lexer.Type (BuiltinName(..))
import           Language.PlutusCore.Constant.Prelude
import           Language.PlutusCore.Lexer.Type

import qualified Data.ByteString.Lazy.Char8 as BSL
import           Data.Text.Prettyprint.Doc

infixr 9 `TypeSchemeArrow`

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

data SizeEntry size
    = SizeValue Size
    | SizeBound size
    deriving (Functor)

-- | Built-in types. A type is considired "built-in" if it can appear in the type signature
-- of a primitive operation. So @boolean@ is considered built-in even though it is defined in PLC
-- and is not primitive.
data TypedBuiltin size a where
    TypedBuiltinSized :: SizeEntry size -> TypedBuiltinSized a -> TypedBuiltin size a
    TypedBuiltinBool  :: TypedBuiltin size Bool

data TypedBuiltinValue size a = TypedBuiltinValue (TypedBuiltin size a) a

-- | Type schemes of primitive operations.
data TypeScheme size a where
    TypeSchemeBuiltin :: TypedBuiltin size a -> TypeScheme size a
    TypeSchemeArrow   :: TypeScheme size a -> TypeScheme size b -> TypeScheme size (a -> b)
    TypeSchemeAllSize :: (size -> TypeScheme size a) -> TypeScheme size a
    -- This is nailed to @size@ rather than being a generic @TypeSchemeForall@ for simplicity
    -- and because at the moment we do not need anything else.
    -- We can make this generic by parametrising @TypeScheme@ by an
     -- @f :: Kind () -> *@ rather than @size@.

-- | A 'BuiltinName' with an associated 'TypeScheme'.
data TypedBuiltinName a = TypedBuiltinName
    { _typedBuiltinNameUntyped    :: BuiltinName
    , _typedBuiltinNameTypeScheme :: forall size. TypeScheme size a
    }

instance Pretty BuiltinSized where
    pretty BuiltinSizedInt  = "integer"
    pretty BuiltinSizedBS   = "bytestring"
    pretty BuiltinSizedSize = "size"

instance Pretty (TypedBuiltinSized a) where
    pretty = pretty . eraseTypedBuiltinSized

instance Pretty size => Pretty (SizeEntry size) where
    pretty (SizeValue size) = pretty size
    pretty (SizeBound size) = pretty size

instance Pretty size => Pretty (TypedBuiltin size a) where
    pretty (TypedBuiltinSized sizeEntry tbs) = parens $ pretty tbs <+> pretty sizeEntry
    pretty TypedBuiltinBool                  = "bool"

instance size ~ Size => Pretty (TypedBuiltinValue size a) where
    pretty (TypedBuiltinValue (TypedBuiltinSized size tbs) x) =
        pretty size <+> "!" <+> case tbs of
            TypedBuiltinSizedInt  -> pretty      x
            TypedBuiltinSizedBS   -> prettyBytes x
            TypedBuiltinSizedSize -> pretty      x
    pretty (TypedBuiltinValue TypedBuiltinBool             b) = pretty b

eraseTypedBuiltinSized :: TypedBuiltinSized a -> BuiltinSized
eraseTypedBuiltinSized TypedBuiltinSizedInt  = BuiltinSizedInt
eraseTypedBuiltinSized TypedBuiltinSizedBS   = BuiltinSizedBS
eraseTypedBuiltinSized TypedBuiltinSizedSize = BuiltinSizedSize

flattenSizeEntry :: SizeEntry Size -> Size
flattenSizeEntry (SizeValue size) = size
flattenSizeEntry (SizeBound size) = size

fmapSizeTypedBuiltin :: (size -> size') -> TypedBuiltin size a -> TypedBuiltin size' a
fmapSizeTypedBuiltin f (TypedBuiltinSized se tbs) = TypedBuiltinSized (fmap f se) tbs
fmapSizeTypedBuiltin _ TypedBuiltinBool           = TypedBuiltinBool

sizeIntIntInt :: TypeScheme size (Integer -> Integer -> Integer)
sizeIntIntInt =
    TypeSchemeAllSize $ \s ->
        TypeSchemeBuiltin (TypedBuiltinSized (SizeBound s) TypedBuiltinSizedInt) `TypeSchemeArrow`
        TypeSchemeBuiltin (TypedBuiltinSized (SizeBound s) TypedBuiltinSizedInt) `TypeSchemeArrow`
        TypeSchemeBuiltin (TypedBuiltinSized (SizeBound s) TypedBuiltinSizedInt)

sizeIntIntBool :: TypeScheme size (Integer -> Integer -> Bool)
sizeIntIntBool =
    TypeSchemeAllSize $ \s ->
        TypeSchemeBuiltin (TypedBuiltinSized (SizeBound s) TypedBuiltinSizedInt) `TypeSchemeArrow`
        TypeSchemeBuiltin (TypedBuiltinSized (SizeBound s) TypedBuiltinSizedInt) `TypeSchemeArrow`
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

typedResizeInteger :: TypedBuiltinName (Size -> Integer -> Integer)
typedResizeInteger =
    TypedBuiltinName ResizeInteger $
        TypeSchemeAllSize $ \s0 -> TypeSchemeAllSize $ \s1 ->
            TypeSchemeBuiltin (TypedBuiltinSized (SizeBound s1) TypedBuiltinSizedSize) `TypeSchemeArrow`
            TypeSchemeBuiltin (TypedBuiltinSized (SizeBound s0) TypedBuiltinSizedInt) `TypeSchemeArrow`
            TypeSchemeBuiltin (TypedBuiltinSized (SizeBound s1) TypedBuiltinSizedInt)

typedIntToByteString :: TypedBuiltinName (Size -> Integer -> BSL.ByteString)
typedIntToByteString =
    TypedBuiltinName IntToByteString $
        TypeSchemeAllSize $ \s0 -> TypeSchemeAllSize $ \s1 ->
            TypeSchemeBuiltin (TypedBuiltinSized (SizeBound s1) TypedBuiltinSizedSize) `TypeSchemeArrow`
            TypeSchemeBuiltin (TypedBuiltinSized (SizeBound s0) TypedBuiltinSizedInt) `TypeSchemeArrow`
            TypeSchemeBuiltin (TypedBuiltinSized (SizeBound s1) TypedBuiltinSizedBS)

typedConcatenate :: TypedBuiltinName (BSL.ByteString -> BSL.ByteString -> BSL.ByteString)
typedConcatenate =
    TypedBuiltinName Concatenate $
        TypeSchemeAllSize $ \s ->
            TypeSchemeBuiltin (TypedBuiltinSized (SizeBound s) TypedBuiltinSizedBS) `TypeSchemeArrow`
            TypeSchemeBuiltin (TypedBuiltinSized (SizeBound s) TypedBuiltinSizedBS) `TypeSchemeArrow`
            TypeSchemeBuiltin (TypedBuiltinSized (SizeBound s) TypedBuiltinSizedBS)

typedTakeByteString :: TypedBuiltinName (Integer -> BSL.ByteString -> BSL.ByteString)
typedTakeByteString =
    TypedBuiltinName TakeByteString $
        TypeSchemeAllSize $ \s0 -> TypeSchemeAllSize $ \s1 ->
            TypeSchemeBuiltin (TypedBuiltinSized (SizeBound s0) TypedBuiltinSizedInt) `TypeSchemeArrow`
            TypeSchemeBuiltin (TypedBuiltinSized (SizeBound s1) TypedBuiltinSizedBS) `TypeSchemeArrow`
            TypeSchemeBuiltin (TypedBuiltinSized (SizeBound s1) TypedBuiltinSizedBS)

typedDropByteString :: TypedBuiltinName (Integer -> BSL.ByteString -> BSL.ByteString)
typedDropByteString =
    TypedBuiltinName DropByteString $
        TypeSchemeAllSize $ \s0 -> TypeSchemeAllSize $ \s1 ->
            TypeSchemeBuiltin (TypedBuiltinSized (SizeBound s0) TypedBuiltinSizedInt) `TypeSchemeArrow`
            TypeSchemeBuiltin (TypedBuiltinSized (SizeBound s1) TypedBuiltinSizedBS) `TypeSchemeArrow`
            TypeSchemeBuiltin (TypedBuiltinSized (SizeBound s1) TypedBuiltinSizedBS)

typedSHA2 :: TypedBuiltinName (BSL.ByteString -> BSL.ByteString)
typedSHA2 =
    TypedBuiltinName SHA2 $
        TypeSchemeAllSize $ \s ->
            TypeSchemeBuiltin (TypedBuiltinSized (SizeBound s) TypedBuiltinSizedBS) `TypeSchemeArrow`
            TypeSchemeBuiltin (TypedBuiltinSized (SizeValue 256) TypedBuiltinSizedBS)

typedSHA3 :: TypedBuiltinName (BSL.ByteString -> BSL.ByteString)
typedSHA3 =
    TypedBuiltinName SHA3 $
        TypeSchemeAllSize $ \s ->
            TypeSchemeBuiltin (TypedBuiltinSized (SizeBound s) TypedBuiltinSizedBS) `TypeSchemeArrow`
            TypeSchemeBuiltin (TypedBuiltinSized (SizeValue 256) TypedBuiltinSizedBS)

typedVerifySignature :: TypedBuiltinName (BSL.ByteString -> BSL.ByteString -> BSL.ByteString -> Bool)
typedVerifySignature =
    TypedBuiltinName VerifySignature $
        TypeSchemeAllSize $ \s0 -> TypeSchemeAllSize $ \s1 -> TypeSchemeAllSize $ \s2 ->
            TypeSchemeBuiltin (TypedBuiltinSized (SizeBound s0) TypedBuiltinSizedBS) `TypeSchemeArrow`
            TypeSchemeBuiltin (TypedBuiltinSized (SizeBound s1) TypedBuiltinSizedBS) `TypeSchemeArrow`
            TypeSchemeBuiltin (TypedBuiltinSized (SizeBound s2) TypedBuiltinSizedBS) `TypeSchemeArrow`
            TypeSchemeBuiltin TypedBuiltinBool

typedResizeByteString :: TypedBuiltinName (Size -> BSL.ByteString -> BSL.ByteString)
typedResizeByteString =
    TypedBuiltinName ResizeByteString $
        TypeSchemeAllSize $ \s0 -> TypeSchemeAllSize $ \s1 ->
            TypeSchemeBuiltin (TypedBuiltinSized (SizeBound s1) TypedBuiltinSizedSize) `TypeSchemeArrow`
            TypeSchemeBuiltin (TypedBuiltinSized (SizeBound s0) TypedBuiltinSizedBS) `TypeSchemeArrow`
            TypeSchemeBuiltin (TypedBuiltinSized (SizeBound s1) TypedBuiltinSizedBS)

typedEqByteString :: TypedBuiltinName (BSL.ByteString -> BSL.ByteString -> Bool)
typedEqByteString =
    TypedBuiltinName EqByteString $
        TypeSchemeAllSize $ \s ->
            TypeSchemeBuiltin (TypedBuiltinSized (SizeBound s) TypedBuiltinSizedBS) `TypeSchemeArrow`
            TypeSchemeBuiltin (TypedBuiltinSized (SizeBound s) TypedBuiltinSizedBS) `TypeSchemeArrow`
            TypeSchemeBuiltin TypedBuiltinBool

typedTxHash :: TypedBuiltinName BSL.ByteString
typedTxHash =
    TypedBuiltinName TxHash $
        TypeSchemeBuiltin (TypedBuiltinSized (SizeValue 256) TypedBuiltinSizedBS)
