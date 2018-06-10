{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Language.PlutusCore.TypeRenamer ( kindCheck
                                       , typeCheck
                                       , annotate
                                       , rename
                                       , TypeAnnot
                                       , KindAnnot
                                       , CheckM (..)
                                       , TypeError (..)
                                       ) where

import           Control.Monad.Except
import           Control.Monad.State.Lazy
import qualified Data.ByteString.Lazy     as BSL
import           Data.Functor.Foldable
import qualified Data.IntMap              as IM
import           Language.PlutusCore.Name
import           Language.PlutusCore.Type
import           PlutusPrelude

type TypeAnnot = Maybe (Type ())
type KindAnnot = Maybe (Kind ())

type KindContext = IM.IntMap (Kind ())
type TypeContext = IM.IntMap (Type ())

-- step 1: kind checking?
-- We need a state monad for kind checking...

data CheckState = CheckState { kindContext :: KindContext
                             , typeContext :: TypeContext
                             }

emptyState :: CheckState
emptyState = CheckState mempty mempty

data TypeError = KindMismatch (Kind ()) (Kind ())
               | InternalError

-- all builtin types have the same kind
builtinKind :: Kind ()
builtinKind = KindArrow () (Size ()) (Type ())

newtype CheckM a = CheckM { unCheckM :: StateT CheckState (Either TypeError) a }
    deriving (Functor, Applicative, Monad, MonadState CheckState, MonadError TypeError)

extract :: Type a -> a
extract (TyApp x _ _)    = x
extract (TyVar x _)      = x
extract (TyFun x _ _)    = x
extract (TyFix x _ _ _)  = x
extract (TyForall x _ _) = x
extract (TyBuiltin x _)  = x
extract (TyLam x _ _ _)  = x

annotate :: Term TypeAnnot -> Either TypeError (Term TypeAnnot)
annotate = flip evalStateT emptyState . unCheckM . typeCheck

-- TODO: throw an error at the end if type-checking is ambiguous?
-- TODO: figure out a way to "assume" things for added context?
kindCheck :: Type KindAnnot -> CheckM (Type KindAnnot)
kindCheck (TyVar Nothing n) = do
    kSt <- gets kindContext
    let maybeKind = IM.lookup (unUnique $ nameUnique n) kSt
    pure $ TyVar maybeKind n
kindCheck (TyBuiltin Nothing x) =
    pure (TyBuiltin (Just builtinKind) x)
kindCheck (TyFun Nothing t t') = do
    t0 <- extract <$> kindCheck t
    t1 <- extract <$> kindCheck t'
    if t0 == pure (Type ()) && t1 ==  pure (Type ())
        then pure (TyFun (Just (Type ())) t t')
        else throwError InternalError -- TODO do something better here
kindCheck x = pure x

typeCheck :: Term TypeAnnot -> CheckM (Term TypeAnnot)
typeCheck (Var Nothing n) = do
    tSt <- gets typeContext
    let maybeType = IM.lookup (unUnique $ nameUnique n) tSt
    pure $ Var maybeType n
typeCheck x = pure x

type IdentifierM = State IdentifierState

-- This renames terms so that they have a unique identifier. This is useful
-- because of scoping.
rename :: IdentifierState -> Program a -> Program a
rename st (Program x v p) = Program x v (evalState (renameTerm p) st)

insertName :: Int -> BSL.ByteString -> IdentifierM ()
insertName u s = modify (first (IM.insert u s))

-- This has to be matched on lazily because findMax may fail. This won't be
-- a problem as long if the first lookup succeeds, however.
defMax :: Int -> IdentifierM (Maybe BSL.ByteString, Int)
defMax u = (,) <$> gets (IM.lookup u . fst) <*> gets (fst . IM.findMax . fst)

-- TODO: just reuse the information from parsing
-- in fact, until we do this, it will fail.
renameTerm :: Term a -> IdentifierM (Term a)
renameTerm v@(Var _ (Name _ s (Unique u))) =
    insertName u s >>
    pure v
renameTerm t@(LamAbs x (Name x' s (Unique u)) ty t') = do
    insertName u s
    ~(pastDef, m) <- defMax u
    case pastDef of
        Just _ -> LamAbs x (Name x' s (Unique $ m+1)) ty <$> renameTerm (rewriteWith (Unique u) (Unique $ m+1) t')
        _      -> pure t
renameTerm t@(Wrap x (Name x' s (Unique u)) ty t') = do
    insertName u s
    ~(pastDef, m) <- defMax u
    case pastDef of
        Just _ -> Wrap x (Name x' s (Unique $ m+1)) ty <$> renameTerm (rewriteWith (Unique u) (Unique $ m+1) t')
        _      -> pure t
renameTerm (TyInst x t tys) = TyInst x <$> renameTerm t <*> traverse renameType tys
renameTerm (Apply x t ts)   = Apply x <$> renameTerm t <*> traverse renameTerm ts
renameTerm (Unwrap x t)     = Unwrap x <$> renameTerm t
renameTerm x                = pure x

rewriteType :: Unique -> Unique -> Type a -> Type a
rewriteType i j = cata a where
    a (TyVarF x (Name x' s i')) | i == i' =
        TyVar x (Name x' s j)
    a (TyLamF x (Name x' s i') k ty) | i == i' =
        TyLam x (Name x' s j) k ty
    a x = embed x

-- rename a particular unique in a subterm
rewriteWith :: Unique -> Unique -> Term a -> Term a
rewriteWith i j = cata a where
    a (VarF x (Name x' s i')) | i == i' =
        Var x (Name x' s j)
    a (LamAbsF x (Name x' s i') ty t) | i == i' =
        LamAbs x (Name x' s j) ty t
    a (WrapF x (Name x' s i') ty t) | i == i' =
        Wrap x (Name x' s j) ty t
    a x = embed x

-- TODO do the same thing here
renameType :: Type a -> IdentifierM (Type a)
renameType v@(TyVar _ (Name _ s (Unique u))) =
    insertName u s >>
    pure v
renameType ty@(TyLam x (Name x' s (Unique u)) k ty') = do
    insertName u s
    ~(pastDef, m) <- defMax u
    case pastDef of
        Just _ -> TyLam x (Name x' s (Unique $ m+1)) k <$> renameType (rewriteType (Unique u) (Unique $ m+1) ty')
        _      -> pure ty
renameType x = pure x
