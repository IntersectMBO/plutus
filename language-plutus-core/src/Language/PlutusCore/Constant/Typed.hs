-- | This module assigns types to built-ins.
-- See the @plutus-prototype/language-plutus-core/docs/Constant application.md@
-- article for how this emerged.

{-# LANGUAGE GADTs             #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes        #-}
module Language.PlutusCore.Constant.Typed
    ( BuiltinSized(..)
    , TypedBuiltinSized(..)
    , SizeEntry(..)
    , Builtin(..)
    , TypedBuiltin(..)
    , TypedBuiltinValue(..)
    , TypeScheme(..)
    , TypedBuiltinName(..)
    , flattenSizeEntry
    , eraseTypedBuiltinSized
    , mapSizeEntryTypedBuiltin
    , mapSizeTypedBuiltin
    , closeTypedBuiltin
    , typedBuiltinSizedToType
    , withTypedBuiltinSized
    , withTypedBuiltin
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

import           Language.PlutusCore.Lexer.Type       (BuiltinName (..), TypeBuiltin (..), prettyBytes)
import           Language.PlutusCore.Name
import           Language.PlutusCore.PrettyCfg
import           Language.PlutusCore.Quote
import           Language.PlutusCore.StdLib.Data.Bool
import           Language.PlutusCore.Type
import           PlutusPrelude

import qualified Data.ByteString.Lazy.Char8           as BSL
import           Data.GADT.Compare

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
    = SizeValue Size  -- ^ A constant size.
    | SizeBound size  -- ^ A bound size variable.
    deriving (Eq, Ord, Functor)
-- We write @SizeEntry Size@ sometimes, so this data type is not perfect, but it works fine.

data Builtin size
    = BuiltinSized (SizeEntry size) BuiltinSized
    | BuiltinBool

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

-- | A 'BuiltinName' with an associated 'TypeScheme'.
data TypedBuiltinName a r = TypedBuiltinName BuiltinName (forall size. TypeScheme size a r)
-- I attempted to unify various typed things, but sometimes type variables must be universally
-- quantified, sometimes they must be existentially quatified. And those are distinct type variables.

-- I tried using the 'dependent-sum-template' package,
-- but see https://stackoverflow.com/q/50048842/3237465
instance GEq TypedBuiltinSized where
    TypedBuiltinSizedInt  `geq` TypedBuiltinSizedInt  = Just Refl
    TypedBuiltinSizedBS   `geq` TypedBuiltinSizedBS   = Just Refl
    TypedBuiltinSizedSize `geq` TypedBuiltinSizedSize = Just Refl
    _                     `geq` _                     = Nothing

instance Eq size => GEq (TypedBuiltin size) where
    TypedBuiltinSized size1 tbs1 `geq` TypedBuiltinSized size2 tbs2 = do
        guard $ size1 == size2
        tbs1 `geq` tbs2
    TypedBuiltinBool             `geq` TypedBuiltinBool             = Just Refl
    _                            `geq` _                            = Nothing

liftOrdering :: Ordering -> GOrdering a a
liftOrdering LT = GLT
liftOrdering EQ = GEQ
liftOrdering GT = GGT

instance Ord size => GCompare (TypedBuiltin size) where
    TypedBuiltinSized size1 tbs1 `gcompare` TypedBuiltinSized size2 tbs2
        | Just Refl <- tbs1 `geq` tbs2 = liftOrdering $ size1 `compare` size2
        | otherwise                    = case (tbs1, tbs2) of
            (TypedBuiltinSizedInt , _                    ) -> GLT
            (TypedBuiltinSizedBS  , TypedBuiltinSizedInt ) -> GGT
            (TypedBuiltinSizedBS  , _                    ) -> GLT
            (TypedBuiltinSizedSize, _                    ) -> GGT
    TypedBuiltinBool             `gcompare` TypedBuiltinBool      = GEQ
    TypedBuiltinSized _ _        `gcompare` TypedBuiltinBool      = GLT
    TypedBuiltinBool             `gcompare` TypedBuiltinSized _ _ = GGT

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
    pretty (TypedBuiltinSized se tbs) = parens $ pretty tbs <+> pretty se
    pretty TypedBuiltinBool           = "bool"

instance size ~ Size => Pretty (TypedBuiltinValue size a) where
    pretty (TypedBuiltinValue (TypedBuiltinSized se tbs) x) =
        pretty se <+> "!" <+> case tbs of
            TypedBuiltinSizedInt  -> pretty      x
            TypedBuiltinSizedBS   -> prettyBytes x
            TypedBuiltinSizedSize -> pretty      x
    pretty (TypedBuiltinValue TypedBuiltinBool             b) = pretty b

instance size ~ Size => PrettyCfg (TypedBuiltinValue size a)

eraseTypedBuiltinSized :: TypedBuiltinSized a -> BuiltinSized
eraseTypedBuiltinSized TypedBuiltinSizedInt  = BuiltinSizedInt
eraseTypedBuiltinSized TypedBuiltinSizedBS   = BuiltinSizedBS
eraseTypedBuiltinSized TypedBuiltinSizedSize = BuiltinSizedSize

flattenSizeEntry :: SizeEntry Size -> Size
flattenSizeEntry (SizeValue size) = size
flattenSizeEntry (SizeBound size) = size

mapSizeEntryTypedBuiltin
    :: (SizeEntry size -> SizeEntry size') -> TypedBuiltin size a -> TypedBuiltin size' a
mapSizeEntryTypedBuiltin f (TypedBuiltinSized se tbs) = TypedBuiltinSized (f se) tbs
mapSizeEntryTypedBuiltin _ TypedBuiltinBool           = TypedBuiltinBool

mapSizeTypedBuiltin
    :: (size -> size') -> TypedBuiltin size a -> TypedBuiltin size' a
mapSizeTypedBuiltin = mapSizeEntryTypedBuiltin . fmap

closeTypedBuiltin :: TypedBuiltin Size a -> TypedBuiltin b a
closeTypedBuiltin = mapSizeEntryTypedBuiltin $ SizeValue . flattenSizeEntry

typedBuiltinSizedToType :: TypedBuiltinSized a -> Type TyName ()
typedBuiltinSizedToType TypedBuiltinSizedInt  = TyBuiltin () TyInteger
typedBuiltinSizedToType TypedBuiltinSizedBS   = TyBuiltin () TyByteString
typedBuiltinSizedToType TypedBuiltinSizedSize = TyBuiltin () TySize

withTypedBuiltinSized :: BuiltinSized -> (forall a. TypedBuiltinSized a -> c) -> c
withTypedBuiltinSized BuiltinSizedInt  k = k TypedBuiltinSizedInt
withTypedBuiltinSized BuiltinSizedBS   k = k TypedBuiltinSizedBS
withTypedBuiltinSized BuiltinSizedSize k = k TypedBuiltinSizedSize

withTypedBuiltin :: Builtin size -> (forall a. TypedBuiltin size a -> c) -> c
withTypedBuiltin (BuiltinSized se b) k = withTypedBuiltinSized b $ k . TypedBuiltinSized se
withTypedBuiltin BuiltinBool         k = k TypedBuiltinBool

typeSchemeResult :: TypeScheme () a r -> TypedBuiltin () r
typeSchemeResult (TypeSchemeBuiltin tb)   = tb
typeSchemeResult (TypeSchemeArrow _ schB) = typeSchemeResult schB
typeSchemeResult (TypeSchemeAllSize schK) = typeSchemeResult (schK ())

typedBuiltinToType :: TypedBuiltin (Type TyName ()) a -> Quote (Type TyName ())
typedBuiltinToType (TypedBuiltinSized se tbs) =
    return . TyApp () (typedBuiltinSizedToType tbs) $ case se of
        SizeValue size -> TyInt () size
        SizeBound ty   -> ty
typedBuiltinToType TypedBuiltinBool           = getBuiltinBool

typeSchemeToType :: TypeScheme (Type TyName ()) a r -> Quote (Type TyName ())
typeSchemeToType (TypeSchemeBuiltin tb)      = typedBuiltinToType tb
typeSchemeToType (TypeSchemeArrow schA schB) =
    TyFun () <$> typeSchemeToType schA <*> typeSchemeToType schB
typeSchemeToType (TypeSchemeAllSize schK)    =
    freshTyName () "s" >>= typeSchemeToType . schK . TyVar ()

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

-- | Typed 'AddInteger'.
typedAddInteger :: TypedBuiltinName (Integer -> Integer -> Integer) Integer
typedAddInteger = TypedBuiltinName AddInteger sizeIntIntInt

-- | Typed 'SubtractInteger'.
typedSubtractInteger :: TypedBuiltinName (Integer -> Integer -> Integer) Integer
typedSubtractInteger = TypedBuiltinName SubtractInteger sizeIntIntInt

-- | Typed 'MultiplyInteger'.
typedMultiplyInteger :: TypedBuiltinName (Integer -> Integer -> Integer) Integer
typedMultiplyInteger = TypedBuiltinName MultiplyInteger sizeIntIntInt

-- | Typed 'DivideInteger'.
typedDivideInteger :: TypedBuiltinName (Integer -> Integer -> Integer) Integer
typedDivideInteger = TypedBuiltinName DivideInteger sizeIntIntInt

-- | Typed 'RemainderInteger'.
typedRemainderInteger :: TypedBuiltinName (Integer -> Integer -> Integer) Integer
typedRemainderInteger = TypedBuiltinName RemainderInteger sizeIntIntInt

-- | Typed 'LessThanInteger'.
typedLessThanInteger :: TypedBuiltinName (Integer -> Integer -> Bool) Bool
typedLessThanInteger = TypedBuiltinName LessThanInteger sizeIntIntBool

-- | Typed 'LessThanEqInteger'.
typedLessThanEqInteger :: TypedBuiltinName (Integer -> Integer -> Bool) Bool
typedLessThanEqInteger = TypedBuiltinName LessThanEqInteger sizeIntIntBool

-- | Typed 'GreaterThanInteger'.
typedGreaterThanInteger :: TypedBuiltinName (Integer -> Integer -> Bool) Bool
typedGreaterThanInteger = TypedBuiltinName GreaterThanInteger sizeIntIntBool

-- | Typed 'GreaterThanEqInteger'.
typedGreaterThanEqInteger :: TypedBuiltinName (Integer -> Integer -> Bool) Bool
typedGreaterThanEqInteger = TypedBuiltinName GreaterThanEqInteger sizeIntIntBool

-- | Typed 'EqInteger'.
typedEqInteger :: TypedBuiltinName (Integer -> Integer -> Bool) Bool
typedEqInteger = TypedBuiltinName EqInteger sizeIntIntBool

-- | Typed 'ResizeInteger'.
typedResizeInteger :: TypedBuiltinName (Size -> Integer -> Integer) Integer
typedResizeInteger =
    TypedBuiltinName ResizeInteger $
        TypeSchemeAllSize $ \s0 -> TypeSchemeAllSize $ \s1 ->
            TypeSchemeBuiltin (TypedBuiltinSized (SizeBound s1) TypedBuiltinSizedSize) `TypeSchemeArrow`
            TypeSchemeBuiltin (TypedBuiltinSized (SizeBound s0) TypedBuiltinSizedInt) `TypeSchemeArrow`
            TypeSchemeBuiltin (TypedBuiltinSized (SizeBound s1) TypedBuiltinSizedInt)

-- | Typed 'IntToByteString'.
typedIntToByteString :: TypedBuiltinName (Size -> Integer -> BSL.ByteString) BSL.ByteString
typedIntToByteString =
    TypedBuiltinName IntToByteString $
        TypeSchemeAllSize $ \s0 -> TypeSchemeAllSize $ \s1 ->
            TypeSchemeBuiltin (TypedBuiltinSized (SizeBound s1) TypedBuiltinSizedSize) `TypeSchemeArrow`
            TypeSchemeBuiltin (TypedBuiltinSized (SizeBound s0) TypedBuiltinSizedInt) `TypeSchemeArrow`
            TypeSchemeBuiltin (TypedBuiltinSized (SizeBound s1) TypedBuiltinSizedBS)

-- | Typed 'Concatenate'.
typedConcatenate :: TypedBuiltinName (BSL.ByteString -> BSL.ByteString -> BSL.ByteString) BSL.ByteString
typedConcatenate =
    TypedBuiltinName Concatenate $
        TypeSchemeAllSize $ \s ->
            TypeSchemeBuiltin (TypedBuiltinSized (SizeBound s) TypedBuiltinSizedBS) `TypeSchemeArrow`
            TypeSchemeBuiltin (TypedBuiltinSized (SizeBound s) TypedBuiltinSizedBS) `TypeSchemeArrow`
            TypeSchemeBuiltin (TypedBuiltinSized (SizeBound s) TypedBuiltinSizedBS)

-- | Typed 'TakeByteString'.
typedTakeByteString :: TypedBuiltinName (Integer -> BSL.ByteString -> BSL.ByteString) BSL.ByteString
typedTakeByteString =
    TypedBuiltinName TakeByteString $
        TypeSchemeAllSize $ \s0 -> TypeSchemeAllSize $ \s1 ->
            TypeSchemeBuiltin (TypedBuiltinSized (SizeBound s0) TypedBuiltinSizedInt) `TypeSchemeArrow`
            TypeSchemeBuiltin (TypedBuiltinSized (SizeBound s1) TypedBuiltinSizedBS) `TypeSchemeArrow`
            TypeSchemeBuiltin (TypedBuiltinSized (SizeBound s1) TypedBuiltinSizedBS)

-- | Typed 'DropByteString'.
typedDropByteString :: TypedBuiltinName (Integer -> BSL.ByteString -> BSL.ByteString) BSL.ByteString
typedDropByteString =
    TypedBuiltinName DropByteString $
        TypeSchemeAllSize $ \s0 -> TypeSchemeAllSize $ \s1 ->
            TypeSchemeBuiltin (TypedBuiltinSized (SizeBound s0) TypedBuiltinSizedInt) `TypeSchemeArrow`
            TypeSchemeBuiltin (TypedBuiltinSized (SizeBound s1) TypedBuiltinSizedBS) `TypeSchemeArrow`
            TypeSchemeBuiltin (TypedBuiltinSized (SizeBound s1) TypedBuiltinSizedBS)

-- | Typed 'SHA2'.
typedSHA2 :: TypedBuiltinName (BSL.ByteString -> BSL.ByteString) BSL.ByteString
typedSHA2 =
    TypedBuiltinName SHA2 $
        TypeSchemeAllSize $ \s ->
            TypeSchemeBuiltin (TypedBuiltinSized (SizeBound s) TypedBuiltinSizedBS) `TypeSchemeArrow`
            TypeSchemeBuiltin (TypedBuiltinSized (SizeValue 256) TypedBuiltinSizedBS)

-- | Typed 'SHA3'.
typedSHA3 :: TypedBuiltinName (BSL.ByteString -> BSL.ByteString) BSL.ByteString
typedSHA3 =
    TypedBuiltinName SHA3 $
        TypeSchemeAllSize $ \s ->
            TypeSchemeBuiltin (TypedBuiltinSized (SizeBound s) TypedBuiltinSizedBS) `TypeSchemeArrow`
            TypeSchemeBuiltin (TypedBuiltinSized (SizeValue 256) TypedBuiltinSizedBS)

-- | Typed 'VerifySignature'.
typedVerifySignature :: TypedBuiltinName (BSL.ByteString -> BSL.ByteString -> BSL.ByteString -> Bool) Bool
typedVerifySignature =
    TypedBuiltinName VerifySignature $
        TypeSchemeAllSize $ \s0 -> TypeSchemeAllSize $ \s1 -> TypeSchemeAllSize $ \s2 ->
            TypeSchemeBuiltin (TypedBuiltinSized (SizeBound s0) TypedBuiltinSizedBS) `TypeSchemeArrow`
            TypeSchemeBuiltin (TypedBuiltinSized (SizeBound s1) TypedBuiltinSizedBS) `TypeSchemeArrow`
            TypeSchemeBuiltin (TypedBuiltinSized (SizeBound s2) TypedBuiltinSizedBS) `TypeSchemeArrow`
            TypeSchemeBuiltin TypedBuiltinBool

-- | Typed 'ResizeByteString'.
typedResizeByteString :: TypedBuiltinName (Size -> BSL.ByteString -> BSL.ByteString) BSL.ByteString
typedResizeByteString =
    TypedBuiltinName ResizeByteString $
        TypeSchemeAllSize $ \s0 -> TypeSchemeAllSize $ \s1 ->
            TypeSchemeBuiltin (TypedBuiltinSized (SizeBound s1) TypedBuiltinSizedSize) `TypeSchemeArrow`
            TypeSchemeBuiltin (TypedBuiltinSized (SizeBound s0) TypedBuiltinSizedBS) `TypeSchemeArrow`
            TypeSchemeBuiltin (TypedBuiltinSized (SizeBound s1) TypedBuiltinSizedBS)

-- | Typed 'EqByteString'.
typedEqByteString :: TypedBuiltinName (BSL.ByteString -> BSL.ByteString -> Bool) Bool
typedEqByteString =
    TypedBuiltinName EqByteString $
        TypeSchemeAllSize $ \s ->
            TypeSchemeBuiltin (TypedBuiltinSized (SizeBound s) TypedBuiltinSizedBS) `TypeSchemeArrow`
            TypeSchemeBuiltin (TypedBuiltinSized (SizeBound s) TypedBuiltinSizedBS) `TypeSchemeArrow`
            TypeSchemeBuiltin TypedBuiltinBool

-- | Typed 'TxHash'.
typedTxHash :: TypedBuiltinName BSL.ByteString BSL.ByteString
typedTxHash =
    TypedBuiltinName TxHash $
        TypeSchemeBuiltin (TypedBuiltinSized (SizeValue 256) TypedBuiltinSizedBS)
