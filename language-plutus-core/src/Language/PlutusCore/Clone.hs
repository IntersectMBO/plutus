{-# LANGUAGE FlexibleContexts #-}

module Language.PlutusCore.Clone ( cloneType
                                 , tyEnvAssign
                                 , TypeSt
                                 ) where

import           Control.Monad.State.Class
import           Data.Functor.Foldable
import qualified Data.IntMap               as IM
import           Language.PlutusCore.Name
import           Language.PlutusCore.Quote
import           Language.PlutusCore.Type
import           PlutusPrelude

type TypeSt = IM.IntMap (NormalizedType TyNameWithKind ())

tyEnvAssign :: MonadState (TypeSt, Natural) m
            => Unique
            -> NormalizedType TyNameWithKind ()
            -> m ()
tyEnvAssign (Unique i) ty = modify (first (IM.insert i ty))

-- | Reduce any redexes inside a type.
cloneType :: MonadQuote m => Type TyNameWithKind a -> m (Type TyNameWithKind a)
cloneType (TyFix l (TyNameWithKind (TyName (Name l' n u))) ty) = do
    u' <- liftQuote freshUnique
    TyFix l (TyNameWithKind (TyName (Name l' n u'))) <$> cloneType (tyRewrite u u' ty)
cloneType (TyForall l (TyNameWithKind (TyName (Name l' n u))) k ty) = do
    u' <- liftQuote freshUnique
    TyForall l (TyNameWithKind (TyName (Name l' n u'))) k <$> cloneType (tyRewrite u u' ty)
cloneType (TyLam l (TyNameWithKind (TyName (Name l' n u))) k ty) = do
    u' <- liftQuote freshUnique
    TyLam l (TyNameWithKind (TyName (Name l' n u'))) k <$> cloneType (tyRewrite u u' ty)
cloneType (TyApp l ty ty') = TyApp l <$> cloneType ty <*> cloneType ty'
cloneType (TyFun l ty ty') = TyFun l <$> cloneType ty <*> cloneType ty'
cloneType x@TyVar{}        = pure x
cloneType x@TyBuiltin{}    = pure x
cloneType x@TyInt{}        = pure x

tyRewrite :: Unique -> Unique -> Type TyNameWithKind a -> Type TyNameWithKind a
tyRewrite u u' = cata a where
    a (TyVarF l (TyNameWithKind (TyName (Name l' n u'')))) | u == u'' = TyVar l (TyNameWithKind (TyName (Name l' n u')))
    a x                                                   = embed x
