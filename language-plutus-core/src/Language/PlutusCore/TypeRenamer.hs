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
rename :: IdentifierState -> Program TyName Name a -> Program TyName Name a
rename (st, _) (Program x v p) = Program x v (evalState (renameTerm (Identifiers st') p) m)
    where st' = IM.fromList (zip keys keys)
          keys = IM.keys st
          m = fst (IM.findMax st)

newtype Identifiers = Identifiers { _identifiers :: IM.IntMap Int }
    deriving Show

type MaxM = State Int

identifiers :: Lens' Identifiers (IM.IntMap Int)
identifiers f s = fmap (\x -> s { _identifiers = x }) (f (_identifiers s))

-- FIXME renameType and renameTerm should not be independent?
renameTerm :: Identifiers -> Term TyName Name a -> MaxM (Term TyName Name a)
renameTerm st t@(LamAbs x (Name x' s (Unique u)) ty t') =
    case pastDef of
        Just _ -> LamAbs x (Name x' s (Unique (m+1))) <$> (renameType st' ty) <*> (renameTerm st' t')
        _      -> pure t
    where st' = over identifiers (IM.insert u (m+1) . IM.insert (m+1) (m+1)) st
          m = fst (IM.findMax (_identifiers st))
          pastDef = IM.lookup u (_identifiers st)
renameTerm st t@(Var x (Name x' s (Unique u))) =
    case pastDef of
        Just j -> pure $ Var x (Name x' s (Unique j))
        _      -> pure t
    where pastDef = IM.lookup u (_identifiers st)
renameTerm st (Apply x t ts) = Apply x <$> (renameTerm st t) <*> (traverse (renameTerm st) ts)
renameTerm _ x = pure x

renameType :: Identifiers -> Type TyName a -> MaxM (Type TyName a)
renameType _ = pure
