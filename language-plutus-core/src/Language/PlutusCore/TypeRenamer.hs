{-# LANGUAGE FlexibleContexts #-}

module Language.PlutusCore.TypeRenamer ( rename
                                       ) where

import           Control.Monad.State.Lazy
import qualified Data.ByteString.Lazy     as BSL
import           Data.Functor.Foldable    hiding (Fix (..))
import qualified Data.IntMap              as IM
import           Language.PlutusCore.Name
import           Language.PlutusCore.Type
import           PlutusPrelude

type IdentifierM = State IdentifierState

-- This renames terms so that they have a unique identifier. This is useful
-- because of scoping.
rename :: IdentifierState -> Program Name a -> Program Name a
rename st (Program x v p) = Program x v (evalState (renameTerm p) st)

insertName :: Int -> BSL.ByteString -> IdentifierM ()
insertName u s = modify (first (IM.insert u s))

-- This has to be matched on lazily because findMax may fail. This won't be
-- a problem as long if the first lookup succeeds, however.
defMax :: Int -> IdentifierM (Maybe BSL.ByteString, Int)
defMax u = (,) <$> gets (IM.lookup u . fst) <*> gets (fst . IM.findMax . fst)

-- TODO: just reuse the information from parsing
-- in fact, until we do this, it will fail.
renameTerm :: Term Name a -> IdentifierM (Term Name a)
renameTerm v@(Var _ (Name _ s (Unique u))) =
    insertName u s >>
    pure v
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
renameTerm t@(Wrap x (Name x' s (Unique u)) ty t') = do
    insertName u s
    ~(pastDef, m) <- defMax u
    case pastDef of
        Just _ -> Wrap x (Name x' s (Unique $ m+1)) ty <$> renameTerm (rewriteWith (Unique u) (Unique $ m+1) t')
        _      -> pure t
renameTerm t@(TyAbs x (Name x' s (Unique u)) k t') = do
    insertName u s
    ~(pastDef, m) <- defMax u
    case pastDef of
        Just _ -> TyAbs x (Name x' s (Unique $ m+1)) k <$> renameTerm (mapType (rewriteType (Unique u) (Unique $ m+1)) t')
        _      -> pure t
renameTerm (TyInst x t tys) = TyInst x <$> renameTerm t <*> traverse renameType tys
renameTerm (Apply x t ts)   = Apply x <$> renameTerm t <*> traverse renameTerm ts
renameTerm (Unwrap x t)     = Unwrap x <$> renameTerm t
renameTerm x                = pure x

-- rename a particular type
rewriteType :: Unique -> Unique -> Type Name a -> Type Name a
rewriteType i j = cata a where
    a (TyVarF x (Name x' s i')) | i == i' =
        TyVar x (Name x' s j)
    a (TyLamF x (Name x' s i') k ty) | i == i' =
        TyLam x (Name x' s j) k ty
    a (TyFixF x (Name x' s i') k ty) | i == i' =
        TyFix x (Name x' s j) k ty
    a (TyForallF x (Name x' s i') k ty) | i == i' =
        TyForall x (Name x' s j) k ty
    a x = embed x

-- rename a particular unique in a subterm
rewriteWith :: Unique -> Unique -> Term Name a -> Term Name a
rewriteWith i j = cata a where
    a (VarF x (Name x' s i')) | i == i' =
        Var x (Name x' s j)
    a (LamAbsF x (Name x' s i') ty t) | i == i' =
        LamAbs x (Name x' s j) ty t
    a (WrapF x (Name x' s i') ty t) | i == i' =
        Wrap x (Name x' s j) ty t
    a (FixF x (Name x' s i') ty t) | i == i' =
        Fix x (Name x' s j) ty t
    a x = embed x

mapType :: (Type Name a -> Type Name a) -> Term Name a -> Term Name a
mapType f (LamAbs x n ty t) = LamAbs x n (f ty) t
mapType f (Fix x n ty t)    = Fix x n (f ty) t
mapType f (Wrap x n ty t)   = Wrap x n (f ty) t
mapType _ x                 = x

renameType :: Type Name a -> IdentifierM (Type Name a)
renameType v@(TyVar _ (Name _ s (Unique u))) =
    insertName u s >>
    pure v
renameType ty@(TyLam x (Name x' s (Unique u)) k ty') = do
    insertName u s
    ~(pastDef, m) <- defMax u
    case pastDef of
        Just _ -> TyLam x (Name x' s (Unique $ m+1)) k <$> renameType (rewriteType (Unique u) (Unique $ m+1) ty')
        _      -> pure ty
renameType ty@(TyForall x (Name x' s (Unique u)) k ty') = do
    insertName u s
    ~(pastDef, m) <- defMax u
    case pastDef of
        Just _ -> TyForall x (Name x' s (Unique $ m+1)) k <$> renameType (rewriteType (Unique u) (Unique $ m+1) ty')
        _      -> pure ty
renameType ty@(TyFix x (Name x' s (Unique u)) k ty') = do
    insertName u s
    ~(pastDef, m) <- defMax u
    case pastDef of
        Just _ -> TyFix x (Name x' s (Unique $ m+1)) k <$> renameType (rewriteType (Unique u) (Unique $ m+1) ty')
        _      -> pure ty
renameType x = pure x
