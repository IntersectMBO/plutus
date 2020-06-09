{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE GADTs            #-}
{-# LANGUAGE RankNTypes       #-}
{-# LANGUAGE TypeApplications #-}

module Language.PlutusCore.Constant.Function
    ( typeSchemeToType
    , dynamicBuiltinNameMeaningToType
    , insertDynamicBuiltinNameDefinition
    , typeOfTypedBuiltinName
    , typeComponentsOfTypedBuiltinName
    , TypeComponents(..)
    , splitTypeScheme
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
typeSchemeToType :: TypeScheme uni as r -> Type TyName uni ()
typeSchemeToType = runQuote . go 0 where
    go :: Int -> TypeScheme uni as r -> Quote (Type TyName uni ())
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
dynamicBuiltinNameMeaningToType :: DynamicBuiltinNameMeaning uni -> Type TyName uni ()
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
typeOfTypedBuiltinName :: TypedBuiltinName uni as r -> Type TyName uni ()
typeOfTypedBuiltinName (TypedBuiltinName _ scheme) = typeSchemeToType scheme

-- | Return the 'Type' of a 'TypedBuiltinName'.
typeComponentsOfTypedBuiltinName :: TypedBuiltinName uni as r -> Maybe (TypeComponents uni)
typeComponentsOfTypedBuiltinName (TypedBuiltinName _ scheme) = splitTypeScheme scheme

{- | A type to represent types of built-in functions in a convenient
   form. We need this because the mapping from TypeSchemes to Types
   isn't injective: eg, a function taking one int argument and returning
   a function of type int -> int has the same type as a function taking
   two integers and returning an int (ie int -> int -> int).
-}
data TypeComponents uni = TypeComponents { tcTypeVars   :: [TyName]
                                         , tcArgTypes   :: [Type TyName uni ()]
                                         , tcResultType :: Type TyName uni ()}

{- | splitTypeScheme takes a type scheme of the form

      forall a1 ... forall aK . ty1 -> ... -> tyN -> resultTy

   (possibly K and/or N are 0) and converts it into

      TypeComoponents [a1,...,aK] [ty1,...,tyK] resultTy

   It actually returns a Maybe, failing if the type scheme is of the
   wrong form (for instance, with a `forall` in the middle).  This can
   probably be done a lot more cleanly.
-}
splitTypeScheme :: TypeScheme uni args res -> Maybe (TypeComponents uni)
splitTypeScheme = split1 []
    where split1 :: [TyName] -> TypeScheme uni args res -> Maybe (TypeComponents uni)
          split1 tynames (TypeSchemeResult r)           = Just $ TypeComponents (reverse tynames) [] (toTypeAst r) -- Only type variables, no types
          split1 tynames (TypeSchemeArrow tyA schB)     = split2 tynames [toTypeAst tyA] schB  -- At the end of the type variables, look for types
          split1 tynames (TypeSchemeAllType proxy schK) = -- Found a type variable
              case proxy of
                (_ :: Proxy '(text, uniq)) ->
                    let text   = Text.pack $ symbolVal @text Proxy
                        uniq   = fromIntegral $ natVal @uniq Proxy
                        tyname = TyName $ Name text $ Unique uniq
                    in split1 (tyname : tynames) (schK Proxy)

          split2 :: [TyName] -> [Type TyName uni ()] -> TypeScheme uni args res -> Maybe (TypeComponents uni)
          split2 tynames argtys (TypeSchemeResult r)       = Just $ TypeComponents (reverse tynames) (reverse argtys) (toTypeAst r)  -- Nothing left
          split2 tynames argtys (TypeSchemeArrow tyA schB) = split2 tynames (toTypeAst tyA : argtys) schB  -- Found a type
          split2 _ _ (TypeSchemeAllType _ _ )              = Nothing  -- Found a type variable after a type


