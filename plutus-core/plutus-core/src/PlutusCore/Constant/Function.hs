{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE GADTs            #-}
{-# LANGUAGE TypeApplications #-}

module PlutusCore.Constant.Function
    ( typeSchemeToType
    , countTermArgs
    , ArgumentClass (..)
    , Arity
    , getArity
    ) where

import           PlutusCore.Constant.Typed
import           PlutusCore.Core
import           PlutusCore.Name

import           Data.Proxy
import qualified Data.Text                 as Text
import           GHC.TypeLits

-- | Convert a 'TypeScheme' to the corresponding 'Type'.
-- Basically, a map from the PHOAS representation to the FOAS one.
typeSchemeToType :: TypeScheme term args res -> Type TyName (UniOf term) ()
typeSchemeToType (TypeSchemeResult pR)      = toTypeAst pR
typeSchemeToType (TypeSchemeArrow pA schB)  = TyFun () (toTypeAst pA) $ typeSchemeToType schB
typeSchemeToType (TypeSchemeAll proxy schK) = case proxy of
    (_ :: Proxy '(text, uniq, kind)) ->
        let text = Text.pack $ symbolVal @text Proxy
            uniq = fromIntegral $ natVal @uniq Proxy
            a    = TyName $ Name text $ Unique uniq
        in TyForall () a (knownKind $ Proxy @kind) $ typeSchemeToType (schK Proxy)

countTermArgs :: TypeScheme uni args res -> Int
countTermArgs (TypeSchemeResult _)     = 0
countTermArgs (TypeSchemeArrow _ schB) = 1 + countTermArgs schB
countTermArgs (TypeSchemeAll _ schK)   = countTermArgs (schK Proxy)

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
getArity (TypeSchemeAll _ schK)   = TypeArg : getArity (schK Proxy)
