{-# LANGUAGE MonadComprehensions #-}

module Language.PlutusCore.TypeSynthesis ( kindOf
                                         , typeOf
                                         , typeEq
                                         ) where

import           Control.Monad.Except
import           Control.Monad.Reader
import qualified Data.Map                        as M
import           Language.PlutusCore.Name
import           Language.PlutusCore.Type
import           Language.PlutusCore.TypeRenamer

type BuiltinTable a = M.Map (Constant a) (Type TyName a)
type TypeCheckM a = ReaderT (BuiltinTable a) (Either (TypeError a))

data TypeError a = NotImplemented

isType :: Kind a -> Bool
isType Type{} = True
isType _      = False

kindOf :: Type TyNameWithKind a -> TypeCheckM a (Kind ())
kindOf (TyFun _ ty' ty'') = do
    k <- kindOf ty'
    k' <- kindOf ty''
    if isType k && isType k'
        then pure (Type ())
        else throwError NotImplemented
kindOf (TyForall _ _ _ ty) = do
    k <- kindOf ty
    if isType k
        then pure (Type ())
        else throwError NotImplemented
kindOf (TyLam _ _ k ty) =
    [ KindArrow () (void k) k' | k' <- kindOf ty ]
kindOf _ = throwError NotImplemented

typeOf :: Term NameWithType TyNameWithKind a -> TypeCheckM a (Type TyNameWithKind ())
typeOf _ = throwError NotImplemented

typeEq :: Type TyNameWithKind () -> Type TyNameWithKind () -> Bool
typeEq _ _ = False
