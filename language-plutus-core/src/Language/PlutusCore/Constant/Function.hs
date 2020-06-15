{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE GADTs            #-}
{-# LANGUAGE RankNTypes       #-}
{-# LANGUAGE TypeApplications #-}

module Language.PlutusCore.Constant.Function
    ( typeSchemeToType
    , dynamicBuiltinNameMeaningToType
    , insertDynamicBuiltinNameDefinition
    , typeOfTypedBuiltinName
    , typeComponentsOfTypeScheme
    , typeComponentsOfTypedBuiltinName
    , typeComponentsOfDynamicBuiltinNameMeaning
    , TypeComponents(..)
    ) where

import           Language.PlutusCore.Constant.Typed
import           Language.PlutusCore.Core
import           Language.PlutusCore.Name

import qualified Data.Map                           as Map
import           Data.Proxy
import qualified Data.Text                          as Text
import           GHC.TypeLits

-- | Convert a 'TypeScheme' to the corresponding 'Type'.
-- Basically, a map from the PHOAS representation to the FOAS one.
typeSchemeToType :: TypeScheme uni as r -> Type TyName uni ()
typeSchemeToType (TypeSchemeResult pR)          = toTypeAst pR
typeSchemeToType (TypeSchemeArrow pA schB)      =
    TyFun () (toTypeAst pA) $ typeSchemeToType schB
typeSchemeToType (TypeSchemeAllType proxy schK) = case proxy of
    (_ :: Proxy '(text, uniq)) ->
        let text = Text.pack $ symbolVal @text Proxy
            uniq = fromIntegral $ natVal @uniq Proxy
            a    = TyName $ Name text $ Unique uniq
        in TyForall () a (Type ()) $ typeSchemeToType (schK Proxy)

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

{- | A type to represent types of built-in functions in a convenient
   form.  We can't use the Type because that's ambiguous: eg, a
   function taking one int argument and returning a function of type
   int -> int has the same Type as a function taking two integers and
   returning an int (ie int -> int -> int).  TypeSchemes for builtins
   contain the information we require, but are a bit too general,
   allowing one to represent types that builtins aren't allowed to
   have (builtins have to have types with all quantifiers at the
   start, but TypeSchemes can represent types with quantifiers in the
   middle).  The TypeComponents type represents exactly the types we
   need for typechecking builtins, which simplifies typechecking.  The
   typeComponentsOfTypeScheme function attempts to convert a
   TypeScheme to a TypeComponents object.
-}
data TypeComponents uni = TypeComponents { tcTypeVars   :: [TyName]
                                         , tcArgTypes   :: [Type TyName uni ()]
                                         , tcResultType :: Type TyName uni ()}

{- | typeComponentsOfTypeScheme takes a type scheme of the form

      forall a1 ... forall aK . ty1 -> ... -> tyN -> resultTy

   (possibly K and/or N are 0) and converts it into

      TypeComoponents [a1,...,aK] [ty1,...,tyK] resultTy

   It actually returns a Maybe, failing if the type scheme is of the
   wrong form (for instance, with a `forall` in the middle).  This can
   probably be done a lot more cleanly.
-}
typeComponentsOfTypeScheme :: TypeScheme uni args res -> Maybe (TypeComponents uni)
typeComponentsOfTypeScheme = split1 []
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


-- | Return the 'TypeComponents' of a 'TypedBuiltinName'.
typeComponentsOfTypedBuiltinName :: TypedBuiltinName uni as r -> Maybe (TypeComponents uni)
typeComponentsOfTypedBuiltinName (TypedBuiltinName _ scheme) = typeComponentsOfTypeScheme scheme

-- | Return the 'TypeComponents' of a 'DynamicBuiltinNameMeaning'.
typeComponentsOfDynamicBuiltinNameMeaning :: DynamicBuiltinNameMeaning uni -> Maybe (TypeComponents uni)
typeComponentsOfDynamicBuiltinNameMeaning (DynamicBuiltinNameMeaning scheme _ _) = typeComponentsOfTypeScheme scheme
