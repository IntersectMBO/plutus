module Language.PlutusCore.Clone ( cloneType
                                 ) where

import           Data.Functor.Foldable
import           Language.PlutusCore.Name
import           Language.PlutusCore.Quote
import           Language.PlutusCore.Type

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
