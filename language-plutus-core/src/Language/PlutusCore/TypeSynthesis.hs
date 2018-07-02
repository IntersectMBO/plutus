{-# LANGUAGE MonadComprehensions #-}

module Language.PlutusCore.TypeSynthesis ( kindOf
                                         , typeOf
                                         ) where

import           Control.Monad.Except
import           Control.Monad.Reader
import qualified Data.Map                        as M
import           Language.PlutusCore.Lexer.Type
import           Language.PlutusCore.Name
import           Language.PlutusCore.Type
import           Language.PlutusCore.TypeRenamer
import qualified Data.List.NonEmpty as NE
import           PlutusPrelude

data BuiltinTable a = BuiltinTable (M.Map TypeBuiltin (Kind a)) (M.Map BuiltinName (Type TyNameWithKind a))
type TypeCheckM a = ReaderT (BuiltinTable a) (Either (TypeError a))

data TypeError a = NotImplemented
                 | InternalError
                 | KindMismatch -- TODO this should be more detailed
                 | TypeMismatch

isType :: Kind a -> Bool
isType Type{} = True
isType _      = False

kindOf :: Type TyNameWithKind a -> TypeCheckM a (Kind ())
kindOf (TyFun _ ty' ty'') = do
    k <- kindOf ty'
    k' <- kindOf ty''
    if isType k && isType k'
        then pure (Type ())
        else throwError KindMismatch
kindOf (TyForall _ _ _ ty) = do
    k <- kindOf ty
    if isType k
        then pure (Type ())
        else throwError KindMismatch
kindOf (TyLam _ _ k ty) =
    [ KindArrow () (void k) k' | k' <- kindOf ty ]
kindOf (TyVar _ (TyNameWithKind (TyName (Name (_, k) _ _)))) = pure (void k)
kindOf (TyBuiltin _ b) = do
    (BuiltinTable tyst _) <- ask
    case M.lookup b tyst of
        Just k -> pure (void k)
        _      -> throwError InternalError
kindOf (TyFix _ _ ty) = do
    k <- kindOf ty
    if isType k
        then pure (Type ())
        else throwError KindMismatch
kindOf (TyApp _ ty (ty' :| [])) = do
    k <- kindOf ty
    case k of
        KindArrow _ k' k'' -> do
            k''' <- kindOf ty'
            if k'' == k'''
                then pure k'
                else throwError KindMismatch
        _ -> throwError KindMismatch
kindOf (TyApp x ty (ty' :| tys)) =
    kindOf (TyApp x (TyApp x ty (ty' :| [])) (NE.fromList tys))

integerType :: Natural -> Type a ()
integerType _ = TyBuiltin () TyInteger

bsType :: Natural -> Type a ()
bsType _ = TyBuiltin () TyByteString

typeOf :: Term TyNameWithKind NameWithType a -> TypeCheckM a (Type TyNameWithKind ())
typeOf (Var _ (NameWithType (Name (_, ty) _ _))) = pure (void ty)
typeOf (Fix _ _ _ t)                             = typeOf t
typeOf (LamAbs _ _ ty t)                         = TyFun () (void ty) <$> typeOf t
typeOf (Error _ ty)                              = pure (void ty) -- FIXME should check that it has appropriate kind?
typeOf (TyAbs _ n k t)                           = TyForall () (void n) (void k) <$> typeOf t
typeOf (Constant _ (BuiltinName _ n)) = do
    (BuiltinTable _ st) <- ask
    case M.lookup n st of
        Just k -> pure (void k)
        _      -> throwError InternalError
typeOf (Constant _ (BuiltinInt _ n _))           = pure (integerType n)
typeOf (Constant _ (BuiltinBS _ n _))            = pure (bsType n)
typeOf (Apply _ t (t' :| [])) = do
    ty <- typeOf t
    case ty of
        TyFun _ ty' ty'' -> do
            ty''' <- typeOf t'
            if typeEq ty'' ty'''
                then pure ty'
                else throwError TypeMismatch
        _ -> throwError TypeMismatch
typeOf (Apply x t (t' :| ts)) =
    typeOf (Apply x (Apply x t (t' :| [])) (NE.fromList ts))
typeOf _                                         = throwError NotImplemented -- TODO handle all of these

-- FIXME actually implement this
typeEq :: Type TyNameWithKind () -> Type TyNameWithKind () -> Bool
typeEq _ _ = False
