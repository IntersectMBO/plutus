{-# LANGUAGE MonadComprehensions #-}
{-# LANGUAGE OverloadedStrings   #-}

module Language.PlutusCore.TypeSynthesis ( kindOf
                                         , typeOf
                                         ) where

import           Control.Monad.Except
import           Control.Monad.Reader
import           Data.Functor.Foldable          hiding (Fix (..))
import qualified Data.List.NonEmpty             as NE
import qualified Data.Map                       as M
import           Data.Text.Prettyprint.Doc
import           Language.PlutusCore.Lexer.Type
import           Language.PlutusCore.Name
import           Language.PlutusCore.Renamer
import           Language.PlutusCore.Type
import           PlutusPrelude

-- | A builtin table contains the kinds of builtin types and the types of
-- builtin names.
data BuiltinTable a = BuiltinTable (M.Map TypeBuiltin (Kind a)) (M.Map BuiltinName (Type TyNameWithKind a))
type TypeCheckM a = ReaderT (BuiltinTable a) (Either (TypeError a))

data TypeError a = NotImplemented
                 | InternalError
                 | KindMismatch a (Type TyNameWithKind ()) (Kind ()) (Kind ()) -- TODO this should be more detailed and in particular include a subexpression
                 | TypeMismatch a

instance Pretty a => Pretty (TypeError a) where
    pretty NotImplemented   = "Type synthesis not yet implementd."
    pretty InternalError    = "Internal error."
    pretty (KindMismatch x ty k k') = "Kind mismatch at" <+> pretty x <+> "in type" <+> pretty ty <> ". Expected kind" <+> pretty k <+> ", found kind" <+> pretty k'
    pretty (TypeMismatch x) = "Type mismatch at" <+> pretty x

isType :: Kind a -> Bool
isType Type{} = True
isType _      = False

-- | Extract kind information from a type.
kindOf :: Type TyNameWithKind a -> TypeCheckM a (Kind ())
kindOf (TyFun x ty' ty'') = do
    k <- kindOf ty'
    k' <- kindOf ty''
    if isType k && isType k'
        then pure (Type ())
        else throwError (KindMismatch x undefined undefined undefined)
kindOf (TyForall x _ _ ty) = do
    k <- kindOf ty
    if isType k
        then pure (Type ())
        else throwError (KindMismatch x (void ty) (Type ()) k)
kindOf (TyLam _ _ k ty) =
    [ KindArrow () (void k) k' | k' <- kindOf ty ]
kindOf (TyVar _ (TyNameWithKind (TyName (Name (_, k) _ _)))) = pure (void k)
kindOf (TyBuiltin _ b) = do
    (BuiltinTable tyst _) <- ask
    case M.lookup b tyst of
        Just k -> pure (void k)
        _      -> throwError InternalError
kindOf (TyFix x _ ty) = do
    k <- kindOf ty
    if isType k
        then pure (Type ())
        else throwError (KindMismatch x (void ty) (Type ()) k)
kindOf (TyApp x ty (ty' :| [])) = do
    k <- kindOf ty
    case k of
        KindArrow _ k' k'' -> do
            k''' <- kindOf ty'
            if k'' == k'''
                then pure k'
                else throwError (KindMismatch x (void ty') k'' k''')
        _ -> throwError (KindMismatch x (void ty') undefined k)
kindOf (TyApp x ty (ty' :| tys)) =
    kindOf (TyApp x (TyApp x ty (ty' :| [])) (NE.fromList tys))

integerType :: Natural -> Type a ()
integerType _ = TyBuiltin () TyInteger

bsType :: Natural -> Type a ()
bsType _ = TyBuiltin () TyByteString

sizeType :: Natural -> Type a ()
sizeType _ = TyBuiltin () TySize

-- | Extract type of a term.
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
typeOf (Constant _ (BuiltinSize _ n))            = pure (sizeType n)
typeOf (Apply x t (t' :| [])) = do
    ty <- typeOf t
    case ty of
        TyFun _ ty' ty'' -> do
            ty''' <- typeOf t'
            if typeEq ty'' ty'''
                then pure ty'
                else throwError (TypeMismatch x)
        _ -> throwError (TypeMismatch x)
typeOf (Apply x t (t' :| ts)) =
    typeOf (Apply x (Apply x t (t' :| [])) (NE.fromList ts))
typeOf (TyInst x t (ty :| [])) = do
    ty' <- typeOf t
    case ty' of
        TyForall _ n k ty'' -> do
            k' <- kindOf ty
            if k == k'
                then pure (tySubstitute (extractUnique n) (void ty) ty'')
                else throwError (KindMismatch x (void ty) k k')
        _ -> throwError (TypeMismatch x)
typeOf (TyInst x t (ty :| tys)) =
    typeOf (TyInst x (TyInst x t (ty :| [])) (NE.fromList tys)) -- TODO: is this correct?
typeOf (Unwrap x t) = do
    ty <- typeOf t
    case ty of
        TyFix _ n ty' -> pure (tySubstitute (extractUnique n) ty ty')
        _             -> throwError (TypeMismatch x)
typeOf Wrap{} = throwError NotImplemented -- TODO handle all of these

extractUnique :: TyNameWithKind a -> Unique
extractUnique = nameUnique . unTyName . unTyNameWithKind

tySubstitute :: Unique -- ^ Unique associated with type variable
             -> Type TyNameWithKind a -- ^ Type we are binding to free variable
             -> Type TyNameWithKind a -- ^ Type we are substituting in
             -> Type TyNameWithKind a
tySubstitute u ty = cata a where
    a (TyVarF _ (TyNameWithKind (TyName (Name _ _ u')))) | u == u' = ty
    a x                                                  = embed x
-- TODO: make type substitutions occur in a state monad somewhere?

-- TODO test suite for this
--
-- 1. Possibly use golden tests? Definitely test error messages.
-- 2. Test some nontrivial type inference, e.g. addInteger 1 2 or something
-- 3. Also fix up parser for integer types

-- TODO: checking type normality &c.

-- FIXME actually implement this
typeEq :: Type TyNameWithKind () -> Type TyNameWithKind () -> Bool
typeEq _ _ = False
