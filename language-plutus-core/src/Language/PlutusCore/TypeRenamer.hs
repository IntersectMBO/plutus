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
import qualified Data.IntMap              as IM
import           Language.PlutusCore.Name
import           Language.PlutusCore.Type

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
extract (TyApp x _ _)      = x
extract (TyVar x _)        = x
extract (TyFun x _ _)      = x
extract (TyFix x _ _ _)    = x
extract (TyForall x _ _ _) = x
extract (TyBuiltin x _)    = x
extract (TyLam x _ _ _)    = x

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

-- This renames terms so that they have a unique identifier. This is useful
-- because of scoping.
rename :: Term a -> Term a
rename = id
