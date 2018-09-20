{-# LANGUAGE MonadComprehensions #-}

module Language.PlutusCore.Clone ( cloneType
                                 ) where

import           Data.Functor.Foldable
import           Language.PlutusCore.Name
import           Language.PlutusCore.Quote
import           Language.PlutusCore.Type

cloneType :: MonadQuote m => Type TyNameWithKind a -> m (Type TyNameWithKind a)
cloneType (TyFix l (TyNameWithKind (TyName (Name l' n u))) ty) = [ TyFix l (TyNameWithKind (TyName (Name l' n u'))) (tyRewrite u u' ty) | u' <- liftQuote freshUnique ]
cloneType (TyForall l (TyNameWithKind (TyName (Name l' n u))) k ty) = [ TyForall l (TyNameWithKind (TyName (Name l' n u'))) k (tyRewrite u u' ty) | u' <- liftQuote freshUnique ]
cloneType (TyLam l (TyNameWithKind (TyName (Name l' n u))) k ty) = [ TyLam l (TyNameWithKind (TyName (Name l' n u'))) k (tyRewrite u u' ty) | u' <- liftQuote freshUnique ]
cloneType (TyApp l ty ty') = TyApp l <$> cloneType ty <*> cloneType ty'
cloneType (TyFun l ty ty') = TyFun l <$> cloneType ty <*> cloneType ty'
cloneType x@TyVar{}        = pure x
cloneType x@TyBuiltin{}    = pure x
cloneType x@TyInt{}        = pure x

tyRewrite :: Unique -> Unique -> Type TyNameWithKind a -> Type TyNameWithKind a
tyRewrite u u' = cata a where
    a (TyVarF l (TyNameWithKind (TyName (Name l' n u'')))) | u == u'' = TyVar l (TyNameWithKind (TyName (Name l' n u')))
    a x                                                   = embed x
