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
import           Language.PlutusCore.Name
import           Language.PlutusCore.Quote
import           Language.PlutusCore.Type

import qualified Data.Map                           as Map
import           Data.Proxy
import qualified Data.Text                          as Text
import           GHC.TypeLits

-- | Convert a 'TypeScheme' to the corresponding 'Type'.
-- Basically, a map from the PHOAS representation to the FOAS one.
typeSchemeToType :: TypeScheme a r -> Type TyName ()
typeSchemeToType = runQuote . go 0 where
    go :: Int -> TypeScheme a r -> Quote (Type TyName ())
    go _ (TypeSchemeResult pR)          = pure $ toTypeAst pR
    go i (TypeSchemeArrow pA schB)    =
        TyFun () (toTypeAst pA) <$> go i schB
    go i (TypeSchemeAllType proxy schK) = case proxy of
        (_ :: Proxy '(text, uniq)) -> do
            let text = Text.pack $ symbolVal @text Proxy
                uniq = fromIntegral $ natVal @uniq Proxy
                a    = TyName $ Name () text $ Unique uniq
            TyForall () a (Type ()) <$> go i (schK Proxy)

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
