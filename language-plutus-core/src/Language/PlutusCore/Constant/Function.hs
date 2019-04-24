{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE GADTs            #-}
{-# LANGUAGE RankNTypes       #-}
{-# LANGUAGE TypeApplications #-}

module Language.PlutusCore.Constant.Function
    (eraseTypedBuiltinStatic
    , typedBuiltinStaticToType
    , withTypedBuiltinStatic
    , typedBuiltinToType
    , typeSchemeToType
    , dynamicBuiltinNameMeaningToType
    , insertDynamicBuiltinNameDefinition
    , typeOfTypedBuiltinName
    ) where

import           Language.PlutusCore.Constant.Typed
import           Language.PlutusCore.Lexer.Type     hiding (name)
import           Language.PlutusCore.Name
import           Language.PlutusCore.Quote
import           Language.PlutusCore.Type

import qualified Data.Map                           as Map
import           Data.Proxy
import qualified Data.Text                          as Text
import           GHC.TypeLits

-- | Convert a 'TypedBuiltinStatic' to the corresponding 'TypeBuiltin' and
-- wrap the result in 'TyBuiltin' to get a 'Type'.
typedBuiltinStaticToType :: TypedBuiltinStatic a -> Type TyName ()
typedBuiltinStaticToType TypedBuiltinStaticInt = TyBuiltin () TyInteger
typedBuiltinStaticToType TypedBuiltinStaticBS  = TyBuiltin () TyByteString

-- | Apply a continuation to the typed version of a 'BuiltinSized'.
withTypedBuiltinStatic :: BuiltinStatic -> (forall a. TypedBuiltinStatic a -> c) -> c
withTypedBuiltinStatic BuiltinStaticInt  k = k TypedBuiltinStaticInt
withTypedBuiltinStatic BuiltinStaticBS   k = k TypedBuiltinStaticBS

-- | Convert a 'TypedBuiltin' to the corresponding 'Type'.
typedBuiltinToType :: TypedBuiltin a -> Type TyName ()
typedBuiltinToType (TypedBuiltinStatic tbs) = typedBuiltinStaticToType tbs
typedBuiltinToType dyn@TypedBuiltinDyn     = toTypeEncoding dyn

-- | Convert a 'TypeScheme' to the corresponding 'Type'.
-- Basically, a map from the PHOAS representation to the FOAS one.
typeSchemeToType :: TypeScheme a r -> Type TyName ()
typeSchemeToType = runQuote . go 0 where
    go :: Int -> TypeScheme a r -> Quote (Type TyName ())
    go _ (TypeSchemeBuiltin tb)         = pure $ typedBuiltinToType tb
    go i (TypeSchemeArrow schA schB)    =
        TyFun () <$> go i schA <*> go i schB
    go i (TypeSchemeAllType proxy schK) = case proxy of
        (_ :: Proxy '(text, uniq)) -> do
            let text = Text.pack $ symbolVal @text Proxy
                uniq = fromIntegral $ natVal @uniq Proxy
                a    = TyName $ Name () text $ Unique uniq
            TyForall () a (Type ()) <$> go i (schK TypedBuiltinDyn)

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
