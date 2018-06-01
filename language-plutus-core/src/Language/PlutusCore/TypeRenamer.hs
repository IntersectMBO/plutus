{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Language.PlutusCore.TypeRenamer ( rename
                                       , fill
                                       , kindCheck
                                       , typeCheck
                                       , TypeAnnot
                                       , CheckM (..)
                                       , CheckState (..)
                                       , TypeError (..)
                                       ) where

import           Control.Monad.Except
import           Control.Monad.State.Lazy
import           Data.Functor.Foldable
import qualified Data.IntMap                    as IM
import           Language.PlutusCore.Lexer.Type
import           Language.PlutusCore.Name
import           Language.PlutusCore.Type
import           PlutusPrelude

type TypeAnnot = Maybe (Type ())
type KindAnnot = Maybe (Kind ())

fill :: Type a -> Type (Maybe a)
fill = fmap (pure Nothing)

squish :: Type a -> Type ()
squish = fmap (pure mempty)

type KindContext = IM.IntMap (Kind ())
type TypeContext = IM.IntMap (Type ())

-- step 1: kind checking?
-- We need a state monad for kind checking...

data CheckState = CheckState { kindContext :: KindContext
                             , typeContext :: TypeContext
                             }

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

-- TODO: how should we handle this? should it be based on the judgment rules?
-- If so, it should be relatively easy, however, I need to know it will
-- terminate. Ideally I could cite the spec.
-- Maybe that should just be in a function called typecheck or the like?
--
-- we should also annotate each 'TyVar' with the kind of its binder.
-- | Annotate each 'Var' with the type of its binder.
rename :: Term TypeAnnot -> Term TypeAnnot
rename = ana a where
    a (TyAnnot _ t (Var _ n))                                                  = VarF (Just (squish t)) n
    a (Apply _ (Constant _ (BuiltinName _ AddInteger)) (Var _ _ :| [Var _ _])) = undefined
    a x                                                                        = project x
