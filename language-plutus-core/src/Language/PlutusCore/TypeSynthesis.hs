{-# LANGUAGE MonadComprehensions #-}

module Language.PlutusCore.TypeSynthesis ( kindOf
                                         , typeOf
                                         , typeEq
                                         ) where

import           Control.Monad.Except
import           Control.Monad.Reader
import qualified Data.Map                        as M
import           Language.PlutusCore.Lexer.Type
import           Language.PlutusCore.Name
import           Language.PlutusCore.Type
import           Language.PlutusCore.TypeRenamer

newtype BuiltinTable a = BuiltinTable (M.Map TypeBuiltin (Kind a))
type TypeCheckM table a = ReaderT (table a) (Either (TypeError a))

data TypeError a = NotImplemented
                 | InternalError

isType :: Kind a -> Bool
isType Type{} = True
isType _      = False

kindOf :: Type TyNameWithKind a -> TypeCheckM BuiltinTable a (Kind ())
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
kindOf (TyVar _ (TyNameWithKind (TyName (Name (_, k) _ _)))) = pure (void k)
kindOf (TyBuiltin _ b) = do
    (BuiltinTable tyst) <- ask
    case M.lookup b tyst of
        Just k -> pure (void k)
        _      -> throwError InternalError
kindOf (TyFix _ _ ty) = do
    k <- kindOf ty
    if isType k
        then pure (Type ())
        else throwError NotImplemented
kindOf _ = throwError NotImplemented

typeOf :: Term NameWithType TyNameWithKind a -> TypeCheckM BuiltinTable a (Type TyNameWithKind ())
typeOf _ = throwError NotImplemented

typeEq :: Type TyNameWithKind () -> Type TyNameWithKind () -> Bool
typeEq _ _ = False
