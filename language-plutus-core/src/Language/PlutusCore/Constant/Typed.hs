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
    , Typed(..)
    , flattenSizeEntry
    , eraseTypedBuiltinSized
    , fmapSizeTypedBuiltin
    , typedBuiltinSizedToType
    , typeSchemeResult
    , typedBuiltinToType
    , typeSchemeToType
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
import           Language.PlutusCore.Name
import           Language.PlutusCore.Type
import           Language.PlutusCore.Lexer.Type (BuiltinName(..), TypeBuiltin(..), prettyBytes)
import           Language.PlutusCore.Constant.Prelude

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
data TypeScheme size a r where
    TypeSchemeBuiltin :: TypedBuiltin size a -> TypeScheme size a a
    TypeSchemeArrow   :: TypeScheme size a q -> TypeScheme size b r -> TypeScheme size (a -> b) r
    TypeSchemeAllSize :: (size -> TypeScheme size a r) -> TypeScheme size a r
    -- This is nailed to @size@ rather than being a generic @TypeSchemeForall@ for simplicity
    -- and because at the moment we do not need anything else.
    -- We can make this generic by parametrising @TypeScheme@ by an
     -- @f :: Kind () -> *@ rather than @size@.

-- | A type with an associated 'TypeScheme'.
data Typed v a r = Typed
    { _typedValue  :: v
    , _typedScheme :: forall size. TypeScheme size a r
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

typedBuiltinSizedToType :: TypedBuiltinSized a -> Type TyName ()
typedBuiltinSizedToType TypedBuiltinSizedInt  = TyBuiltin () TyInteger
typedBuiltinSizedToType TypedBuiltinSizedBS   = TyBuiltin () TyByteString
typedBuiltinSizedToType TypedBuiltinSizedSize = TyBuiltin () TySize

typeSchemeResult :: TypeScheme (Maybe size) a r -> TypedBuiltin (Maybe size) r
typeSchemeResult (TypeSchemeBuiltin tb)   = tb
typeSchemeResult (TypeSchemeArrow _ schB) = typeSchemeResult schB
typeSchemeResult (TypeSchemeAllSize schK) = typeSchemeResult (schK Nothing)

typedBuiltinToType :: TypedBuiltin (TyName ()) a -> Fresh (Type TyName ())
typedBuiltinToType (TypedBuiltinSized sizeEntry tbs) =
    return . TyApp () (typedBuiltinSizedToType tbs) $ case sizeEntry of
        SizeValue size -> TyInt () size
        SizeBound name -> TyVar () name
typedBuiltinToType TypedBuiltinBool                  = getBuiltinBool

typeSchemeToType :: TypeScheme (TyName ()) a r -> Fresh (Type TyName ())
typeSchemeToType (TypeSchemeBuiltin tb)      = typedBuiltinToType tb
typeSchemeToType (TypeSchemeArrow schA schB) =
    TyFun () <$> typeSchemeToType schA <*> typeSchemeToType schB
typeSchemeToType (TypeSchemeAllSize schK)    = do
    s <- freshTyName () "s"
    typeSchemeToType $ schK s

sizeIntIntInt :: TypeScheme size (Integer -> Integer -> Integer) Integer
sizeIntIntInt =
    TypeSchemeAllSize $ \s ->
        TypeSchemeBuiltin (TypedBuiltinSized (SizeBound s) TypedBuiltinSizedInt) `TypeSchemeArrow`
        TypeSchemeBuiltin (TypedBuiltinSized (SizeBound s) TypedBuiltinSizedInt) `TypeSchemeArrow`
        TypeSchemeBuiltin (TypedBuiltinSized (SizeBound s) TypedBuiltinSizedInt)

sizeIntIntBool :: TypeScheme size (Integer -> Integer -> Bool) Bool
sizeIntIntBool =
    TypeSchemeAllSize $ \s ->
        TypeSchemeBuiltin (TypedBuiltinSized (SizeBound s) TypedBuiltinSizedInt) `TypeSchemeArrow`
        TypeSchemeBuiltin (TypedBuiltinSized (SizeBound s) TypedBuiltinSizedInt) `TypeSchemeArrow`
        TypeSchemeBuiltin TypedBuiltinBool

typedAddInteger :: Typed BuiltinName (Integer -> Integer -> Integer) Integer
typedAddInteger = Typed AddInteger sizeIntIntInt

typedSubtractInteger :: Typed BuiltinName (Integer -> Integer -> Integer) Integer
typedSubtractInteger = Typed SubtractInteger sizeIntIntInt

typedMultiplyInteger :: Typed BuiltinName (Integer -> Integer -> Integer) Integer
typedMultiplyInteger = Typed MultiplyInteger sizeIntIntInt

typedDivideInteger :: Typed BuiltinName (Integer -> Integer -> Integer) Integer
typedDivideInteger = Typed DivideInteger sizeIntIntInt

typedRemainderInteger :: Typed BuiltinName (Integer -> Integer -> Integer) Integer
typedRemainderInteger = Typed RemainderInteger sizeIntIntInt

typedLessThanInteger :: Typed BuiltinName (Integer -> Integer -> Bool) Bool
typedLessThanInteger = Typed LessThanInteger sizeIntIntBool

typedLessThanEqInteger :: Typed BuiltinName (Integer -> Integer -> Bool) Bool
typedLessThanEqInteger = Typed LessThanEqInteger sizeIntIntBool

typedGreaterThanInteger :: Typed BuiltinName (Integer -> Integer -> Bool) Bool
typedGreaterThanInteger = Typed GreaterThanInteger sizeIntIntBool

typedGreaterThanEqInteger :: Typed BuiltinName (Integer -> Integer -> Bool) Bool
typedGreaterThanEqInteger = Typed GreaterThanEqInteger sizeIntIntBool

typedEqInteger :: Typed BuiltinName (Integer -> Integer -> Bool) Bool
typedEqInteger = Typed EqInteger sizeIntIntBool

typedResizeInteger :: Typed BuiltinName (Size -> Integer -> Integer) Integer
typedResizeInteger =
    Typed ResizeInteger $
        TypeSchemeAllSize $ \s0 -> TypeSchemeAllSize $ \s1 ->
            TypeSchemeBuiltin (TypedBuiltinSized (SizeBound s1) TypedBuiltinSizedSize) `TypeSchemeArrow`
            TypeSchemeBuiltin (TypedBuiltinSized (SizeBound s0) TypedBuiltinSizedInt) `TypeSchemeArrow`
            TypeSchemeBuiltin (TypedBuiltinSized (SizeBound s1) TypedBuiltinSizedInt)

typedIntToByteString :: Typed BuiltinName (Size -> Integer -> BSL.ByteString) BSL.ByteString
typedIntToByteString =
    Typed IntToByteString $
        TypeSchemeAllSize $ \s0 -> TypeSchemeAllSize $ \s1 ->
            TypeSchemeBuiltin (TypedBuiltinSized (SizeBound s1) TypedBuiltinSizedSize) `TypeSchemeArrow`
            TypeSchemeBuiltin (TypedBuiltinSized (SizeBound s0) TypedBuiltinSizedInt) `TypeSchemeArrow`
            TypeSchemeBuiltin (TypedBuiltinSized (SizeBound s1) TypedBuiltinSizedBS)

typedConcatenate :: Typed BuiltinName (BSL.ByteString -> BSL.ByteString -> BSL.ByteString) BSL.ByteString
typedConcatenate =
    Typed Concatenate $
        TypeSchemeAllSize $ \s ->
            TypeSchemeBuiltin (TypedBuiltinSized (SizeBound s) TypedBuiltinSizedBS) `TypeSchemeArrow`
            TypeSchemeBuiltin (TypedBuiltinSized (SizeBound s) TypedBuiltinSizedBS) `TypeSchemeArrow`
            TypeSchemeBuiltin (TypedBuiltinSized (SizeBound s) TypedBuiltinSizedBS)

typedTakeByteString :: Typed BuiltinName (Integer -> BSL.ByteString -> BSL.ByteString) BSL.ByteString
typedTakeByteString =
    Typed TakeByteString $
        TypeSchemeAllSize $ \s0 -> TypeSchemeAllSize $ \s1 ->
            TypeSchemeBuiltin (TypedBuiltinSized (SizeBound s0) TypedBuiltinSizedInt) `TypeSchemeArrow`
            TypeSchemeBuiltin (TypedBuiltinSized (SizeBound s1) TypedBuiltinSizedBS) `TypeSchemeArrow`
            TypeSchemeBuiltin (TypedBuiltinSized (SizeBound s1) TypedBuiltinSizedBS)

typedDropByteString :: Typed BuiltinName (Integer -> BSL.ByteString -> BSL.ByteString) BSL.ByteString
typedDropByteString =
    Typed DropByteString $
        TypeSchemeAllSize $ \s0 -> TypeSchemeAllSize $ \s1 ->
            TypeSchemeBuiltin (TypedBuiltinSized (SizeBound s0) TypedBuiltinSizedInt) `TypeSchemeArrow`
            TypeSchemeBuiltin (TypedBuiltinSized (SizeBound s1) TypedBuiltinSizedBS) `TypeSchemeArrow`
            TypeSchemeBuiltin (TypedBuiltinSized (SizeBound s1) TypedBuiltinSizedBS)

typedSHA2 :: Typed BuiltinName (BSL.ByteString -> BSL.ByteString) BSL.ByteString
typedSHA2 =
    Typed SHA2 $
        TypeSchemeAllSize $ \s ->
            TypeSchemeBuiltin (TypedBuiltinSized (SizeBound s) TypedBuiltinSizedBS) `TypeSchemeArrow`
            TypeSchemeBuiltin (TypedBuiltinSized (SizeValue 256) TypedBuiltinSizedBS)

typedSHA3 :: Typed BuiltinName (BSL.ByteString -> BSL.ByteString) BSL.ByteString
typedSHA3 =
    Typed SHA3 $
        TypeSchemeAllSize $ \s ->
            TypeSchemeBuiltin (TypedBuiltinSized (SizeBound s) TypedBuiltinSizedBS) `TypeSchemeArrow`
            TypeSchemeBuiltin (TypedBuiltinSized (SizeValue 256) TypedBuiltinSizedBS)

typedVerifySignature :: Typed BuiltinName (BSL.ByteString -> BSL.ByteString -> BSL.ByteString -> Bool) Bool
typedVerifySignature =
    Typed VerifySignature $
        TypeSchemeAllSize $ \s0 -> TypeSchemeAllSize $ \s1 -> TypeSchemeAllSize $ \s2 ->
            TypeSchemeBuiltin (TypedBuiltinSized (SizeBound s0) TypedBuiltinSizedBS) `TypeSchemeArrow`
            TypeSchemeBuiltin (TypedBuiltinSized (SizeBound s1) TypedBuiltinSizedBS) `TypeSchemeArrow`
            TypeSchemeBuiltin (TypedBuiltinSized (SizeBound s2) TypedBuiltinSizedBS) `TypeSchemeArrow`
            TypeSchemeBuiltin TypedBuiltinBool

typedResizeByteString :: Typed BuiltinName (Size -> BSL.ByteString -> BSL.ByteString) BSL.ByteString
typedResizeByteString =
    Typed ResizeByteString $
        TypeSchemeAllSize $ \s0 -> TypeSchemeAllSize $ \s1 ->
            TypeSchemeBuiltin (TypedBuiltinSized (SizeBound s1) TypedBuiltinSizedSize) `TypeSchemeArrow`
            TypeSchemeBuiltin (TypedBuiltinSized (SizeBound s0) TypedBuiltinSizedBS) `TypeSchemeArrow`
            TypeSchemeBuiltin (TypedBuiltinSized (SizeBound s1) TypedBuiltinSizedBS)

typedEqByteString :: Typed BuiltinName (BSL.ByteString -> BSL.ByteString -> Bool) Bool
typedEqByteString =
    Typed EqByteString $
        TypeSchemeAllSize $ \s ->
            TypeSchemeBuiltin (TypedBuiltinSized (SizeBound s) TypedBuiltinSizedBS) `TypeSchemeArrow`
            TypeSchemeBuiltin (TypedBuiltinSized (SizeBound s) TypedBuiltinSizedBS) `TypeSchemeArrow`
            TypeSchemeBuiltin TypedBuiltinBool

typedTxHash :: Typed BuiltinName BSL.ByteString BSL.ByteString
typedTxHash =
    Typed TxHash $
        TypeSchemeBuiltin (TypedBuiltinSized (SizeValue 256) TypedBuiltinSizedBS)
