{-# LANGUAGE FlexibleContexts #-}

module Language.PlutusCore.TypeRenamer ( rename
                                       , annotate
                                       , RenamedTerm
                                       , NameWithType (..)
                                       , RenamedType
                                       , TyNameWithKind (..)
                                       , RenameError (..)
                                       ) where

import           Control.Monad.Except
import           Control.Monad.State.Lazy
import qualified Data.ByteString.Lazy     as BSL
import           Data.Functor.Foldable    hiding (Fix (..))
import qualified Data.IntMap              as IM
import           Language.PlutusCore.Name
import           Language.PlutusCore.Type
import           Lens.Micro
import           PlutusPrelude

data TypeState a = TypeState { _terms :: IM.IntMap (Type TyNameWithKind a), _types :: IM.IntMap (Kind a) }

terms :: Lens' (TypeState a) (IM.IntMap (Type TyNameWithKind a))
terms f s = fmap (\x -> s { _terms = x }) (f (_terms s))

types :: Lens' (TypeState a) (IM.IntMap (Kind a))
types f s = fmap (\x -> s { _types = x }) (f (_types s))

instance Semigroup (TypeState a) where
    (<>) (TypeState x x') (TypeState y y') = TypeState (x <> y) (x' <> y')

instance Monoid (TypeState a) where
    mempty = TypeState mempty mempty
    mappend = (<>)

type IdentifierM = State IdentifierState
type TypeM a = StateT (TypeState a) (Either (RenameError a))

type RenamedTerm a = Term TyNameWithKind NameWithType a
newtype NameWithType a = NameWithType (Name (a, RenamedType a))
type RenamedType a = Type TyNameWithKind a
newtype TyNameWithKind a = TyNameWithKind (TyName (a, Kind a))

data RenameError a = UnboundVar (Name a)
                   | UnboundTyVar (TyName a)
                   | NotImplemented

-- | Annotate a program with type/kind information at all bound variables,
-- failing if we encounter a free variable.
annotate :: Program TyName Name a -> Either (RenameError a) (Program TyNameWithKind NameWithType a)
annotate (Program x v p) = Program x v <$> evalStateT (annotateTerm p) mempty

insertType :: Int -> Type TyNameWithKind a -> TypeM a ()
insertType = modify .* over terms .* IM.insert

insertKind :: Int -> Kind a -> TypeM a ()
insertKind = modify .* over types .* IM.insert

annotateTerm :: Term TyName Name a -> TypeM a (Term TyNameWithKind NameWithType a)
annotateTerm (Var x (Name x' b (Unique u))) = do
    st <- gets _terms
    case IM.lookup u st of
        Just ty -> pure $ Var x (NameWithType (Name (x', ty) b (Unique u)))
        Nothing -> throwError $ UnboundVar (Name x' b (Unique u))
annotateTerm (LamAbs x (Name x' s u@(Unique i)) ty t) = do
    aty <- annotateType ty
    let nwt = NameWithType (Name (x', aty) s u)
    insertType i aty
    LamAbs x nwt aty <$> annotateTerm t
annotateTerm (Fix x (Name x' s u@(Unique i)) ty t) = do
    aty <- annotateType ty
    let nwt = NameWithType (Name (x', aty) s u)
    insertType i aty
    Fix x nwt aty <$> annotateTerm t
annotateTerm (TyAbs x (TyName (Name x' b u@(Unique i))) k t) = do
    insertKind i k
    let nwty = TyNameWithKind (TyName (Name (x', k) b u))
    TyAbs x nwty k <$> annotateTerm t
annotateTerm (Unwrap x t) =
    Unwrap x <$> annotateTerm t
annotateTerm (Error x ty) =
    Error x <$> annotateType ty
annotateTerm (Apply x t ts) =
    Apply x <$> annotateTerm t <*> traverse annotateTerm ts
annotateTerm (Constant x c) =
    pure (Constant x c)
annotateTerm (TyInst x t tys) =
    TyInst x <$> annotateTerm t <*> traverse annotateType tys
annotateTerm Wrap{} = throwError NotImplemented -- TODO don't do this

annotateType :: Type TyName a -> TypeM a (Type TyNameWithKind a)
annotateType (TyVar x (TyName (Name x' b (Unique u)))) = do
    st <- gets _types
    case IM.lookup u st of
        Just ty -> pure $ TyVar x (TyNameWithKind (TyName (Name (x', ty) b (Unique u))))
        Nothing -> throwError $ UnboundVar (Name x' b (Unique u))
annotateType (TyLam x (TyName (Name x' s u@(Unique i))) k ty) = do
    insertKind i k
    let nwty = TyNameWithKind (TyName (Name (x', k) s u))
    TyLam x nwty k <$> annotateType ty
annotateType (TyForall x (TyName (Name x' s u@(Unique i))) k ty) = do
    insertKind i k
    let nwty = TyNameWithKind (TyName (Name (x', k) s u))
    TyForall x nwty k <$> annotateType ty
annotateType (TyFix x (TyName (Name x' s u@(Unique i))) k ty) = do
    insertKind i k
    let nwty = TyNameWithKind (TyName (Name (x', k) s u))
    TyFix x nwty k <$> annotateType ty
annotateType (TyFun x ty ty') =
    TyFun x <$> annotateType ty <*> annotateType ty'
annotateType (TyApp x ty tys) =
    TyApp x <$> annotateType ty <*> traverse annotateType tys
annotateType (TyBuiltin x tyb) = pure (TyBuiltin x tyb)

-- This renames terms so that they have a unique identifier. This is useful
-- because of scoping.
rename :: Program TyName Name a -> Program TyName Name a
rename (Program x v p) = Program x v (evalState (renameTerm p) mempty)

insertName :: Int -> BSL.ByteString -> IdentifierM ()
insertName u s = modify (first (IM.insert u s))

-- This has to be matched on lazily because findMax may fail. This won't be
-- a problem as long if the first lookup succeeds, however.
defMax :: Int -> IdentifierM (Maybe BSL.ByteString, Int)
defMax u = (,) <$> gets (IM.lookup u . fst) <*> gets (fst . IM.findMax . fst)

data Rewrites = Rewrites { _typesRw :: IM.IntMap Int, _termsRw :: IM.IntMap Int }
type RewriteM = State Rewrites

instance Semigroup Rewrites where
    (<>) (Rewrites x y) (Rewrites x' y') = Rewrites (x <> x') (y <> y')

instance Monoid Rewrites where
    mempty = Rewrites mempty mempty

termsRw :: Lens' Rewrites (IM.IntMap Int)
termsRw f s = fmap (\x -> s { _termsRw = x }) (f (_termsRw s))

defMax' :: Int -> RewriteM (Maybe Int, Int)
defMax' u = (,) <$> gets (IM.lookup u . _termsRw) <*> gets (fst . IM.findMax . _termsRw)

insertRw :: Int -> Int -> RewriteM ()
insertRw = modify .* over termsRw .* IM.insert

renameTerm :: Term TyName Name a -> RewriteM (Term TyName Name a)
renameTerm t@(LamAbs x (Name x' s (Unique u)) ty t') = do
    ~(pastDef, m) <- defMax' u
    case pastDef of
        Just _ -> do
            insertRw u (m+1)
            LamAbs x (Name x' s (Unique $ m+1)) ty <$> renameTerm t'
        _      -> pure t
renameTerm t@(Var x (Name x' s (Unique i))) = do
    mn <- gets (IM.lookup i . _termsRw)
    case mn of
        Just j -> pure $ Var x (Name x' s (Unique j))
        _      -> pure t
