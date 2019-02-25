{-# LANGUAGE GADTs             #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes        #-}

module Language.PlutusCore.Constant.Function
    ( flattenSizeEntry
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
    , dynamicBuiltinNameMeaningToType
    , insertDynamicBuiltinNameDefinition
    , typeOfTypedBuiltinName
    ) where

import           Language.PlutusCore.Constant.Typed
import           Language.PlutusCore.Lexer.Type     hiding (name)
import           Language.PlutusCore.Name
import           Language.PlutusCore.Pretty
import           Language.PlutusCore.Quote
import           Language.PlutusCore.Type

import qualified Data.Map                           as Map

-- | Extract the 'Size' from a 'SizeEntry'.
flattenSizeEntry :: SizeEntry Size -> Size
flattenSizeEntry (SizeValue size) = size
flattenSizeEntry (SizeBound size) = size

-- | Alter the 'SizeEntry' of a 'TypedBuiltin'.
mapSizeEntryTypedBuiltin
    :: (SizeEntry size -> SizeEntry size') -> TypedBuiltin size a -> TypedBuiltin size' a
mapSizeEntryTypedBuiltin f (TypedBuiltinSized se tbs) = TypedBuiltinSized (f se) tbs
mapSizeEntryTypedBuiltin _ TypedBuiltinDyn            = TypedBuiltinDyn

-- | Alter the 'size' of a @TypedBuiltin size@.
mapSizeTypedBuiltin
    :: (size -> size') -> TypedBuiltin size a -> TypedBuiltin size' a
mapSizeTypedBuiltin = mapSizeEntryTypedBuiltin . fmap

-- | Map each 'SizeBound' to 'SizeValue'.
closeTypedBuiltin :: TypedBuiltin Size a -> TypedBuiltin b a
closeTypedBuiltin = mapSizeEntryTypedBuiltin $ SizeValue . flattenSizeEntry

-- | Convert a 'TypedBuiltinSized' to the corresponding 'TypeBuiltin' and
-- wrap the result in 'TyBuiltin' to get a 'Type'.
typedBuiltinSizedToType :: TypedBuiltinSized a -> Type TyName ()
typedBuiltinSizedToType TypedBuiltinSizedInt  = TyBuiltin () TyInteger
typedBuiltinSizedToType TypedBuiltinSizedBS   = TyBuiltin () TyByteString
typedBuiltinSizedToType TypedBuiltinSizedSize = TyBuiltin () TySize

-- | Apply a continuation to the typed version of a 'BuiltinSized'.
withTypedBuiltinSized :: BuiltinSized -> (forall a. TypedBuiltinSized a -> c) -> c
withTypedBuiltinSized BuiltinSizedInt  k = k TypedBuiltinSizedInt
withTypedBuiltinSized BuiltinSizedBS   k = k TypedBuiltinSizedBS
withTypedBuiltinSized BuiltinSizedSize k = k TypedBuiltinSizedSize

-- | Apply a continuation to the typed version of a 'Builtin'.
withTypedBuiltin :: BuiltinType size -> (forall a. TypedBuiltin size a -> c) -> c
withTypedBuiltin (BuiltinSized se b) k = withTypedBuiltinSized b $ k . TypedBuiltinSized se

-- | The resulting 'TypedBuiltin' of a 'TypeScheme'.
typeSchemeResult :: TypeScheme () a r -> TypedBuiltin () r
typeSchemeResult (TypeSchemeBuiltin tb)   = tb
typeSchemeResult (TypeSchemeArrow _ schB) = typeSchemeResult schB
typeSchemeResult (TypeSchemeAllSize schK) = typeSchemeResult (schK ())

-- | Convert a 'TypedBuiltin' to the corresponding 'Type'.
typedBuiltinToType :: TypedBuiltin (Type TyName ()) a -> Type TyName ()
typedBuiltinToType (TypedBuiltinSized se tbs) =
    TyApp () (typedBuiltinSizedToType tbs) $ case se of
        SizeValue size -> TyInt () size
        SizeBound ty   -> ty
typedBuiltinToType dyn@TypedBuiltinDyn        = toTypeEncoding dyn

-- | Convert a 'TypeScheme' to the corresponding 'Type'.
-- Basically, a map from the PHOAS representation to the FOAS one.
typeSchemeToType :: TypeScheme (Type TyName ()) a r -> Type TyName ()
typeSchemeToType = runQuote . go 0 where
    go :: Int -> TypeScheme (Type TyName ()) a r -> Quote (Type TyName ())
    go _ (TypeSchemeBuiltin tb)      = pure $ typedBuiltinToType tb
    go i (TypeSchemeArrow schA schB) =
        TyFun () <$> go i schA <*> go i schB
    go i (TypeSchemeAllSize schK)    = do
        s <- freshTyName () $ "s" <> prettyText i
        a <- go (succ i) . schK $ TyVar () s
        return $ TyForall () s (Size ()) a

-- | Extract the 'TypeScheme' from a 'DynamicBuiltinNameMeaning' and
-- convert it to the corresponding 'Type'.
dynamicBuiltinNameMeaningToType :: DynamicBuiltinNameMeaning -> Type TyName ()
dynamicBuiltinNameMeaningToType (DynamicBuiltinNameMeaning sch _) = typeSchemeToType sch

-- | Insert a 'DynamicBuiltinNameDefinition' into a 'DynamicBuiltinNameMeanings'.
insertDynamicBuiltinNameDefinition
    :: DynamicBuiltinNameDefinition -> DynamicBuiltinNameMeanings -> DynamicBuiltinNameMeanings
insertDynamicBuiltinNameDefinition
    (DynamicBuiltinNameDefinition name mean) (DynamicBuiltinNameMeanings nameMeans) =
        DynamicBuiltinNameMeanings $ Map.insert name mean nameMeans

-- | Return the 'Type' of a 'TypedBuiltinName'.
typeOfTypedBuiltinName :: TypedBuiltinName a r -> Type TyName ()
typeOfTypedBuiltinName (TypedBuiltinName _ scheme) = typeSchemeToType scheme
