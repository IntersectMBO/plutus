module Language.PlutusCore.TypeSynthesis.Elimination ( ElimCtx (..)
                                                     , elimSubst
                                                     , getElimCtx
                                                     , extractFix
                                                     ) where

import           Control.Monad.Except                        (MonadError (throwError))
import           Control.Monad.State.Class                   (MonadState)
import           Language.PlutusCore.Error                   (TypeError (..))
import           Language.PlutusCore.Quote                   (MonadQuote)
import           Language.PlutusCore.Type
import           Language.PlutusCore.TypeSynthesis.Normalize
import           Language.PlutusCore.TypeSynthesis.Type
import           PlutusPrelude

data ElimCtx = Hole
             | App ElimCtx (Type TyNameWithKind ())

elimSubst :: ElimCtx -- ^ ℰ
          -> Type TyNameWithKind () -- ^ C
          -> Type TyNameWithKind () -- ^ ℰ{C}
elimSubst Hole ty          = ty
elimSubst (App ctx ty) ty' = TyApp () (elimSubst ctx ty) ty'

getElimCtx :: (MonadError (TypeError a) m, MonadQuote m, MonadState TypeCheckSt m)
           => Term TyNameWithKind NameWithType a
           -> a -- ^ Location
           -> TyNameWithKind a -- ^ α
           -> Type TyNameWithKind a -- ^ S
           -> NormalizedType TyNameWithKind () -- ^ ℰ{[(fix α S)/α] S}
           -> m ElimCtx -- ^ ℰ
getElimCtx t loc alpha s fixSubst = do
    sNorm <- normalizeType (void s) -- FIXME: when should this be normalized?
    typeCheckStep
    subst <- normalizeTypeBinder (void alpha) (TyFix () (void alpha) <$> sNorm) (void s)
    case fixSubst of
        (NormalizedType (TyApp _ ty ty')) | subst /= fixSubst -> App <$> getElimCtx t loc alpha s (NormalizedType ty) <*> pure ty'
        _ | subst == fixSubst                               -> pure Hole
        _                                                   -> throwError (TyElimMismatch loc (void t) (getNormalizedType fixSubst) subst)

-- | Given a type Q, we extract (α, S) such that Q = ℰ{(fix α S)} for some ℰ
extractFix :: MonadError (TypeError a) m
           => Term TyNameWithKind NameWithType a
           -> Type TyNameWithKind () -- ^ Q = ℰ{(fix α S)}
           -> m (TyNameWithKind (), Type TyNameWithKind ()) -- ^ (α, S)
extractFix _ (TyFix _ tn ty) = pure (tn, ty)
extractFix t (TyApp _ ty _)  = extractFix t ty -- can't happen b/c we need ty have to the appropriate kind?
extractFix t ty              = throwError (TyFixMismatch (termLoc t) (void t) (NormalizedType ty)) -- FIXME: don't do this
