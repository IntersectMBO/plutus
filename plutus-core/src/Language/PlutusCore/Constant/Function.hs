{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE GADTs            #-}
{-# LANGUAGE TypeApplications #-}

module Language.PlutusCore.Constant.Function
    ( typeSchemeToType
    , countTermArgs
    , ArgumentClass (..)
    , Arity
    , getArity
    ) where

import           Language.PlutusCore.Constant.Typed
import           Language.PlutusCore.Core
import           Language.PlutusCore.Name

import           Data.Proxy
import qualified Data.Text                          as Text
import           GHC.TypeLits

-- | Convert a 'TypeScheme' to the corresponding 'Type'.
-- Basically, a map from the PHOAS representation to the FOAS one.
typeSchemeToType :: TypeScheme term args res -> Type TyName (UniOf term) ()
typeSchemeToType (TypeSchemeResult pR)           = toTypeAst pR
typeSchemeToType (TypeSchemeArrow pA schB)       = TyFun () (toTypeAst pA) $ typeSchemeToType schB
typeSchemeToType (TypeSchemeAll proxy kind schK) = case proxy of
    (_ :: Proxy '(text, uniq)) ->
        let text = Text.pack $ symbolVal @text Proxy
            uniq = fromIntegral $ natVal @uniq Proxy
            a    = TyName $ Name text $ Unique uniq
        in TyForall () a kind $ typeSchemeToType (schK Proxy)

countTermArgs :: TypeScheme uni args res -> Int
countTermArgs (TypeSchemeResult _)     = 0
countTermArgs (TypeSchemeArrow _ schB) = 1 + countTermArgs schB
countTermArgs (TypeSchemeAll _ _ schK) = countTermArgs (schK Proxy)

-- | This type is used when evaluating builtins to decide whether a term argument or a type instantiation is required
data ArgumentClass
    = TypeArg
    | TermArg
      deriving (Show, Eq)

type Arity = [ArgumentClass]

-- | Return a list containing the argument types of a TypeScheme
getArity ::  TypeScheme uni args res -> Arity
getArity (TypeSchemeResult _)     = []
getArity (TypeSchemeArrow _ schB) = TermArg : getArity schB
getArity (TypeSchemeAll _ _ schK) = TypeArg : getArity (schK Proxy)
