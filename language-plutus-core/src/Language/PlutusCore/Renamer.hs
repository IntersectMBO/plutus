{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleInstances  #-}

module Language.PlutusCore.Renamer (annotateProgram
                                   , annotateTerm
                                   , annotateType
                                   , TypeState (..)
                                   , RenameError (..)
                                   ) where

import           Control.Monad.Except
import           Control.Monad.State.Lazy
import qualified Data.IntMap               as IM
import           Language.PlutusCore.Error
import           Language.PlutusCore.Name
import           Language.PlutusCore.Type
import           Lens.Micro
import           PlutusPrelude

data TypeState a = TypeState { _terms :: IM.IntMap (RenamedType a), _types :: IM.IntMap (Kind a) }

terms :: Lens' (TypeState a) (IM.IntMap (RenamedType a))
terms f s = fmap (\x -> s { _terms = x }) (f (_terms s))

types :: Lens' (TypeState a) (IM.IntMap (Kind a))
types f s = fmap (\x -> s { _types = x }) (f (_types s))

instance Semigroup (TypeState a) where
    (<>) (TypeState x x') (TypeState y y') = TypeState (x <> y) (x' <> y')

instance Monoid (TypeState a) where
    mempty = TypeState mempty mempty
    mappend = (<>)

type TypeM a = StateT (TypeState a) (Either (RenameError a))

-- | Annotate a PLC program, so that all names are annotated with their types/kinds.
annotateProgram :: (MonadError (Error a) m) => Program TyName Name a -> m (Program TyNameWithKind NameWithType a)
annotateProgram (Program a v t) = Program a v <$> annotateTerm t

-- | Annotate a PLC term, so that all names are annotated with their types/kinds.
annotateTerm :: (MonadError (Error a) m) => Term TyName Name a -> m (Term TyNameWithKind NameWithType a)
annotateTerm t = fmap fst $ liftEither $ convertError $ runStateT (annotateT t) mempty

-- | Annotate a PLC type, so that all names are annotated with their types/kinds.
annotateType :: (MonadError (Error a) m) => Type TyName a -> m (Type TyNameWithKind a)
annotateType t = fmap fst $ liftEither $ convertError $ runStateT (annotateTy t) mempty

insertType :: Int -> Type TyNameWithKind a -> TypeM a ()
insertType = modify .* over terms .* IM.insert

insertKind :: Int -> Kind a -> TypeM a ()
insertKind = modify .* over types .* IM.insert

annotateT :: Term TyName Name a -> TypeM a (RenamedTerm a)
annotateT (Var x (Name x' b (Unique u))) = do
    st <- gets _terms
    case IM.lookup u st of
        Just ty -> pure $ Var x (NameWithType (Name (x', ty) b (Unique u)))
        Nothing -> throwError $ UnboundVar (Name x' b (Unique u))
annotateT (LamAbs x (Name x' s u@(Unique i)) ty t) = do
    aty <- annotateTy ty
    let nwt = NameWithType (Name (x', aty) s u)
    insertType i aty
    LamAbs x nwt aty <$> annotateT t
annotateT (TyAbs x (TyName (Name x' b u@(Unique i))) k t) = do
    insertKind i k
    let nwty = TyNameWithKind (TyName (Name (x', k) b u))
    TyAbs x nwty k <$> annotateT t
annotateT (Unwrap x t) =
    Unwrap x <$> annotateT t
annotateT (Error x ty) =
    Error x <$> annotateTy ty
annotateT (Apply x t t') =
    Apply x <$> annotateT t <*> annotateT t'
annotateT (Constant x c) =
    pure (Constant x c)
annotateT (TyInst x t ty) =
    TyInst x <$> annotateT t <*> annotateTy ty
annotateT (Wrap x (TyName (Name x' b u@(Unique i))) ty t) = do
    let k = Type x'
    insertKind i k
    aty <- annotateTy ty
    let nwty = TyNameWithKind (TyName (Name (x', k) b u))
    Wrap x nwty aty <$> annotateT t

annotateTy :: Type TyName a -> TypeM a (RenamedType a)
annotateTy (TyVar x (TyName (Name x' b (Unique u)))) = do
    st <- gets _types
    case IM.lookup u st of
        Just ty -> pure $ TyVar x (TyNameWithKind (TyName (Name (x', ty) b (Unique u))))
        Nothing -> throwError $ UnboundTyVar (TyName (Name x' b (Unique u)))
annotateTy (TyLam x (TyName (Name x' s u@(Unique i))) k ty) = do
    insertKind i k
    let nwty = TyNameWithKind (TyName (Name (x', k) s u))
    TyLam x nwty k <$> annotateTy ty
annotateTy (TyForall x (TyName (Name x' s u@(Unique i))) k ty) = do
    insertKind i k
    let nwty = TyNameWithKind (TyName (Name (x', k) s u))
    TyForall x nwty k <$> annotateTy ty
annotateTy (TyFix x (TyName (Name x' s u@(Unique i))) ty) = do
    let k = Type x'
    insertKind i k
    let nwty = TyNameWithKind (TyName (Name (x', k) s u))
    TyFix x nwty <$> annotateTy ty
annotateTy (TyFun x ty ty') =
    TyFun x <$> annotateTy ty <*> annotateTy ty'
annotateTy (TyApp x ty ty') =
    TyApp x <$> annotateTy ty <*> annotateTy ty'
annotateTy (TyBuiltin x tyb) = pure (TyBuiltin x tyb)
annotateTy (TyInt x n) = pure (TyInt x n)
