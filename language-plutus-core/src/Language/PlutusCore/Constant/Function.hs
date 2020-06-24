{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE GADTs            #-}
{-# LANGUAGE RankNTypes       #-}
{-# LANGUAGE TypeApplications #-}

module Language.PlutusCore.Constant.Function
    ( typeSchemeToType
    , dynamicBuiltinNameMeaningToType
    , insertDynamicBuiltinNameDefinition
    , typeOfTypedBuiltinName
    ) where

import           Language.PlutusCore.Constant.Typed
import           Language.PlutusCore.Core
import           Language.PlutusCore.Name
import           Language.PlutusCore.Quote

import qualified Data.Map                           as Map
import           Data.Proxy
import qualified Data.Text                          as Text
import           GHC.TypeLits

-- | Convert a 'TypeScheme' to the corresponding 'Type'.
-- Basically, a map from the PHOAS representation to the FOAS one.
typeSchemeToType :: UniOf term ~ uni => TypeScheme term as r -> Type TyName uni ()
typeSchemeToType = runQuote . go 0 where
    go :: UniOf term ~ uni => Int -> TypeScheme term as r -> Quote (Type TyName uni ())
    go _ (TypeSchemeResult pR)          = pure $ toTypeAst pR
    go i (TypeSchemeArrow pA schB)      = TyFun () (toTypeAst pA) <$> go i schB
    go i (TypeSchemeAllType proxy schK) = case proxy of
        (_ :: Proxy '(text, uniq)) -> do
            let text = Text.pack $ symbolVal @text Proxy
                uniq = fromIntegral $ natVal @uniq Proxy
                a    = TyName $ Name text $ Unique uniq
            TyForall () a (Type ()) <$> go i (schK Proxy)

-- | Extract the 'TypeScheme' from a 'DynamicBuiltinNameMeaning' and
-- convert it to the corresponding 'Type'.
dynamicBuiltinNameMeaningToType
    :: UniOf term ~ uni => DynamicBuiltinNameMeaning term -> Type TyName uni ()
dynamicBuiltinNameMeaningToType (DynamicBuiltinNameMeaning sch _ _) = typeSchemeToType sch

-- | Insert a 'DynamicBuiltinNameDefinition' into a 'DynamicBuiltinNameMeanings'.
insertDynamicBuiltinNameDefinition
    :: DynamicBuiltinNameDefinition uni
    -> DynamicBuiltinNameMeanings uni
    -> DynamicBuiltinNameMeanings uni
insertDynamicBuiltinNameDefinition
    (DynamicBuiltinNameDefinition name mean) (DynamicBuiltinNameMeanings nameMeans) =
        DynamicBuiltinNameMeanings $ Map.insert name mean nameMeans

-- | Return the 'Type' of a 'TypedBuiltinName'.
typeOfTypedBuiltinName
    :: UniOf term ~ uni => TypedBuiltinName term as r -> Type TyName uni ()
typeOfTypedBuiltinName (TypedBuiltinName _ scheme) = typeSchemeToType scheme
