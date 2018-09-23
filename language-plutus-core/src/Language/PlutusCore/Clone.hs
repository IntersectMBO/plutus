{-# LANGUAGE FlexibleContexts #-}

module Language.PlutusCore.Clone ( cloneType
                                 ) where

import           Control.Monad.State.Class
import           Control.Monad.Trans.State      hiding (get, modify)
import qualified Data.IntMap               as IM
import           Language.PlutusCore.Name
import           Language.PlutusCore.Quote
import           Language.PlutusCore.Type
import PlutusPrelude

type CloneSt = IM.IntMap (TyNameWithKind ())

type CloneM = StateT CloneSt

cloneEnvAssign :: MonadState CloneSt m
               => Unique
               -> TyNameWithKind ()
               -> m ()
cloneEnvAssign (Unique i) ty = modify (IM.insert i ty)

cloneType :: MonadQuote m => Type TyNameWithKind a -> m (Type TyNameWithKind ())
cloneType = flip evalStateT mempty . cloneTypeM

cloneTypeM :: (MonadQuote m) => Type TyNameWithKind a -> CloneM m (Type TyNameWithKind ())
cloneTypeM (TyFix _ (TyNameWithKind (TyName (Name l' n u))) ty) = do
    u' <- liftQuote freshUnique
    let tn = void $ TyNameWithKind (TyName (Name l' n u')) -- TODO use lenses
    cloneEnvAssign u tn
    TyFix () tn <$> cloneTypeM ty
cloneTypeM (TyForall _ (TyNameWithKind (TyName (Name l' n u))) k ty) = do
    u' <- liftQuote freshUnique
    let tn = void $ TyNameWithKind (TyName (Name l' n u'))
    cloneEnvAssign u tn
    TyForall () tn (void k) <$> cloneTypeM ty
cloneTypeM (TyLam _ (TyNameWithKind (TyName (Name l' n u))) k ty) = do
    u' <- liftQuote freshUnique
    let tn = void $ TyNameWithKind (TyName (Name l' n u'))
    cloneEnvAssign u tn
    TyLam () tn (void k) <$> cloneTypeM ty
cloneTypeM (TyApp _ ty ty') = TyApp () <$> cloneTypeM ty <*> cloneTypeM ty'
cloneTypeM (TyFun _ ty ty') = TyFun () <$> cloneTypeM ty <*> cloneTypeM ty'
cloneTypeM x@(TyVar _ (TyNameWithKind (TyName (Name _ _ u)))) = do
    cloneSt <- get
    case IM.lookup (unUnique u) cloneSt of
        Just n -> pure (TyVar () n)
        Nothing -> pure (void x)
cloneTypeM x@TyBuiltin{}    = pure (void x)
cloneTypeM x@TyInt{}        = pure (void x)
