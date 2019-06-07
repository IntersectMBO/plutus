{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE RankNTypes            #-}

-- | This module makes sure types are normalized inside programs.
module Language.PlutusCore.Check.Normal ( checkProgram
                                        , checkTerm
                                        , NormalizationError (..)
                                        , isNormalType
                                        ) where

import           Control.Monad.Except

import           Data.Functor.Foldable
import           Data.Functor.Foldable.Monadic

import           Language.PlutusCore.Error
import           Language.PlutusCore.Name
import           Language.PlutusCore.Type
import           PlutusPrelude

-- | Ensure that all types in the 'Program' are normalized.
checkProgram :: (AsNormalizationError e TyName Name a, MonadError e m) => Program TyName Name a -> m ()
checkProgram (Program _ _ t) = checkTerm t

-- | Ensure that all types in the 'Term' are normalized.
checkTerm :: (AsNormalizationError e TyName Name a, MonadError e m) => Term TyName Name a -> m ()
checkTerm p = void $ throwingEither _NormalizationError $ checkT p

checkT :: Term tyname name a -> Either (NormalizationError tyname name a) (Term tyname name a)
checkT (Error l ty)           = Error l <$> normalType ty
checkT (TyInst l t ty)        = TyInst l <$> checkT t <*> normalType ty
checkT (IWrap l pat arg term) = IWrap l <$> normalType pat <*> normalType arg <*> checkT term
checkT (Unwrap l t)           = Unwrap l <$> checkT t
checkT (LamAbs l n ty t)      = LamAbs l n <$> normalType ty <*> checkT t
checkT (Apply l t1 t2)        = Apply l <$> checkT t1 <*> checkT t2
checkT (TyAbs l tn k t)       = TyAbs l tn k <$> checkT t
checkT t@Var{}                = pure t
checkT t@Constant{}           = pure t
checkT t@Builtin{}            = pure t

{- Note [Builtin applications and values]
An older version of the specification had a special case for builtin type applications being
normal types. This is important, because they obviously can't be reduced before runtime.
This resulted in types like `[(con integer) (con 64)]` not being considered normalized, which
effectively prevents you using integers anywhere (note: this isn't so much of a problem now
integers aren't parameterized, but it's still wrong).

The current version of the specification has moved to fully saturated builtins,
but the implementation is not there. Consequently we consider builtin types to be neutral types.
-}

isNormalType :: Type tyname a -> Bool
isNormalType = isRight . normalType

normalType :: Type tyname a -> Either (NormalizationError tyname name a) (Type tyname a)
normalType (TyFun l i o)        = TyFun l <$> normalType i <*> normalType o
normalType (TyForall l tn k ty) = TyForall l tn k <$> normalType ty
normalType (TyIFix l pat arg)   = TyIFix l <$> normalType pat <*> normalType arg
normalType (TyLam l tn k ty)    = TyLam l tn k <$> normalType ty
normalType ty                   = neutralType ty

neutralType :: Type tyname a -> Either (NormalizationError tyname name a) (Type tyname a)
neutralType ty@TyVar{}        = pure ty
neutralType (TyApp x ty1 ty2) = TyApp x <$> neutralType ty1 <*> normalType ty2
-- See note [Builtin applications and values]
neutralType ty@TyBuiltin{}    = pure ty
neutralType ty                = Left (BadType (tyLoc ty) ty "neutral type")
