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
import qualified Data.IntSet              as IS
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
rename :: IdentifierState -> Program TyName Name a -> Program TyName Name a
rename st (Program x v p) = Program x v (evalState (renameTerm p) st)

insertName :: Int -> BSL.ByteString -> IdentifierM ()
insertName u s = modify (first (IM.insert u s))

-- This has to be matched on lazily because findMax may fail. This won't be
-- a problem as long if the first lookup succeeds, however.
defMax :: Int -> IdentifierM (Maybe BSL.ByteString, Int)
defMax u = (,) <$> gets (IM.lookup u . fst) <*> gets (fst . IM.findMax . fst)

type Rewrites = IM.IntMap Int
type RewriteM = State (IS.IntSet, Rewrites)

-- POSSIBLY consider instead of rewriteWith, just adding to an IntMap and then
-- rewrite down?
renameTerm :: Term TyName Name a -> IdentifierM (Term TyName Name a)
renameTerm t@(LamAbs x (Name x' s (Unique u)) ty t') = do
    insertName u s
    ~(pastDef, m) <- defMax u
    case pastDef of
        Just _ -> LamAbs x (Name x' s (Unique $ m+1)) ty <$> renameTerm (rewriteWith (Unique u) (Unique $ m+1) t')
        _      -> pure t
renameTerm t@(Fix x (Name x' s (Unique u)) ty t') = do
    insertName u s
    ~(pastDef, m) <- defMax u
    case pastDef of
        Just _ -> Fix x (Name x' s (Unique $ m+1)) ty <$> renameTerm (rewriteWith (Unique u) (Unique $ m+1) t')
        _      -> pure t
renameTerm t@(Wrap x (TyName (Name x' s (Unique u))) ty t') = do
    insertName u s
    ~(pastDef, m) <- defMax u
    case pastDef of
        Just _ -> Wrap x (TyName (Name x' s (Unique $ m+1))) ty <$> renameTerm (rewriteWith (Unique u) (Unique $ m+1) t')
        _      -> pure t
renameTerm t@(TyAbs x (TyName (Name x' s (Unique u))) k t') = do
    insertName u s
    ~(pastDef, m) <- defMax u
    case pastDef of
        Just _ -> TyAbs x (TyName (Name x' s (Unique $ m+1))) k <$> renameTerm (mapType (rewriteType (Unique u) (Unique $ m+1)) t')
        _      -> pure t
renameTerm (TyInst x t tys) = TyInst x <$> renameTerm t <*> traverse renameType tys
renameTerm (Apply x t ts)   = Apply x <$> renameTerm t <*> traverse renameTerm ts
renameTerm (Unwrap x t)     = Unwrap x <$> renameTerm t
renameTerm x                = pure x

-- rename a particular type
rewriteType :: Unique -> Unique -> Type TyName a -> Type TyName a
rewriteType i j = cata a where
    a (TyVarF x (TyName (Name x' s i'))) | i == i' =
        TyVar x (TyName (Name x' s j))
    a (TyLamF x (TyName (Name x' s i')) k ty) | i == i' =
        TyLam x (TyName (Name x' s j)) k ty
    a (TyFixF x (TyName (Name x' s i')) k ty) | i == i' =
        TyFix x (TyName (Name x' s j)) k ty
    a (TyForallF x (TyName (Name x' s i')) k ty) | i == i' =
        TyForall x (TyName (Name x' s j)) k ty
    a x = embed x

-- rename a particular unique in a subterm
rewriteWith :: Unique -> Unique -> Term TyName Name a -> Term TyName Name a
rewriteWith i j = cata a where
    a (VarF x (Name x' s i')) | i == i' =
        Var x (Name x' s j)
    a (LamAbsF x (Name x' s i') ty t) | i == i' =
        LamAbs x (Name x' s j) ty t
    a (WrapF x (TyName (Name x' s i')) ty t) | i == i' =
        Wrap x (TyName (Name x' s j)) ty t
    a (FixF x (Name x' s i') ty t) | i == i' =
        Fix x (Name x' s j) ty t
    a x = embed x

mapType :: (Type TyName a -> Type TyName a) -> Term TyName Name a -> Term TyName Name a
mapType f (LamAbs x n ty t) = LamAbs x n (f ty) t
mapType f (Fix x n ty t)    = Fix x n (f ty) t
mapType f (Wrap x n ty t)   = Wrap x n (f ty) t
mapType _ x                 = x

renameType :: Type TyName a -> IdentifierM (Type TyName a)
renameType ty@(TyLam x (TyName (Name x' s (Unique u))) k ty') = do
    insertName u s
    ~(pastDef, m) <- defMax u
    case pastDef of
        Just _ -> TyLam x (TyName (Name x' s (Unique $ m+1))) k <$> renameType (rewriteType (Unique u) (Unique $ m+1) ty')
        _      -> pure ty
renameType ty@(TyForall x (TyName (Name x' s (Unique u))) k ty') = do
    insertName u s
    ~(pastDef, m) <- defMax u
    case pastDef of
        Just _ -> TyForall x (TyName (Name x' s (Unique $ m+1))) k <$> renameType (rewriteType (Unique u) (Unique $ m+1) ty')
        _      -> pure ty
renameType ty@(TyFix x (TyName (Name x' s (Unique u))) k ty') = do
    insertName u s
    ~(pastDef, m) <- defMax u
    case pastDef of
        Just _ -> TyFix x (TyName (Name x' s (Unique $ m+1))) k <$> renameType (rewriteType (Unique u) (Unique $ m+1) ty')
        _      -> pure ty
renameType x = pure x
