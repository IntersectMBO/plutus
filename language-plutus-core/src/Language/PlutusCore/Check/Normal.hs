{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE RankNTypes            #-}

-- | This module makes sure types are normalized inside programs.
module Language.PlutusCore.Check.Normal
    ( checkProgram
    , checkTerm
    , isNormalType
    , NormCheckError (..)
    ) where

import           PlutusPrelude

import           Language.PlutusCore.Core
import           Language.PlutusCore.Error

import           Control.Monad.Except

-- | Ensure that all types in the 'Program' are normalized.
checkProgram
    :: (AsNormCheckError e tyname name ann, MonadError e m)
    => Program tyname name ann -> m ()
checkProgram (Program _ _ t) = checkTerm t

-- | Ensure that all types in the 'Term' are normalized.
checkTerm
    :: (AsNormCheckError e tyname name ann, MonadError e m)
    => Term tyname name ann -> m ()
checkTerm p = throwingEither _NormCheckError $ check p

check :: Term tyname name ann -> Either (NormCheckError tyname name ann) ()
check (Error _ ty)           = normalType ty
check (TyInst _ t ty)        = check t >> normalType ty
check (IWrap _ pat arg term) = normalType pat >> normalType arg >> check term
check (Unwrap _ t)           = check t
check (LamAbs _ _ ty t)      = normalType ty >> check t
check (Apply _ t1 t2)        = check t1 >> check t2
check (TyAbs _ _ _ t)        = check t
check Var{}                  = pure ()
check Constant{}             = pure ()
check Builtin{}              = pure ()

{- Note [Builtin applications and values]
An older version of the specification had a special case for builtin type applications being
normal types. This is important, because they obviously can't be reduced before runtime.
This resulted in types like `[(con integer) (con 64)]` not being considered normalized, which
effectively prevents you using integers anywhere (note: this isn't so much of a problem now
integers aren't parameterized, but it's still wrong).

The current version of the specification has moved to fully saturated builtins,
but the implementation is not there. Consequently we consider builtin types to be neutral types.
-}

isNormalType :: Type tyname ann -> Bool
isNormalType = isRight . normalType

normalType :: Type tyname ann -> Either (NormCheckError tyname name ann) ()
normalType (TyFun _ i o)       = normalType i >> normalType o
normalType (TyForall _ _ _ ty) = normalType ty
normalType (TyIFix _ pat arg)  = normalType pat >> normalType arg
normalType (TyLam _ _ _ ty)    = normalType ty
normalType ty                  = neutralType ty

neutralType :: Type tyname ann -> Either (NormCheckError tyname name ann) ()
neutralType TyVar{}           = pure ()
neutralType (TyApp _ ty1 ty2) = neutralType ty1 >> normalType ty2
-- See note [Builtin applications and values]
neutralType TyBuiltin{}       = pure ()
neutralType ty                = Left (BadType (typeAnn ty) ty "neutral type")
