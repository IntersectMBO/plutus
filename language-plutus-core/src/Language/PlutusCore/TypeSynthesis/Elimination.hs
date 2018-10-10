module Language.PlutusCore.TypeSynthesis.Elimination ( ElimCtx (..)
                                                     , elimSubst
                                                     , getElimCtx
                                                     , extractFix
                                                     ) where

import           Control.Monad.Except
import           Control.Monad.State.Class                   (MonadState)
import           Language.PlutusCore.Error
import           Language.PlutusCore.Quote
import           Language.PlutusCore.Type
import           Language.PlutusCore.TypeSynthesis.Normalize
import           Language.PlutusCore.TypeSynthesis.Type

data ElimCtx = Hole
             | App ElimCtx (Type TyNameWithKind ())

elimSubst :: ElimCtx -- ^ E
          -> Type TyNameWithKind () -- ^ C
          -> Type TyNameWithKind () -- ^ E{C}
elimSubst Hole ty          = ty
elimSubst (App ctx ty) ty' = TyApp () (elimSubst ctx ty) ty'

getElimCtx :: (MonadError (TypeError a) m, MonadQuote m, MonadState TypeCheckSt m)
           => TyNameWithKind () -- ^ a
           -> Type TyNameWithKind () -- ^ S
           -> Type TyNameWithKind () -- ^ E{[(fix a S)/a] S}
           -> m ElimCtx -- ^ E
getElimCtx alpha s fixSubst = do
    sNorm <- normalizeType s
    subst <- normalizeTypeBinder alpha sNorm s
    if getNormalizedType subst == fixSubst then
        pure Hole
    else
        throwError NotImplemented -- FIXME don't do this

-- | Given a type Q, we extract (a, S) such that Q = E{(fix a S)} for some E
extractFix :: MonadError (TypeError a) m
           => Type TyNameWithKind () -- ^ Q = E{(fix a S)}
           -> m (TyNameWithKind (), Type TyNameWithKind ()) -- ^ (a, S)
extractFix (TyFix _ tn ty) = pure (tn, ty)
extractFix (TyApp _ ty _)  = extractFix ty -- can't happen b/c we need ty have to the appropriate kind?
extractFix _               = throwError NotImplemented -- FIXME: don't do this
