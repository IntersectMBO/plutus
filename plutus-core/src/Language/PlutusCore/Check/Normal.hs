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
    :: (AsNormCheckError e tyname name uni fun ann, MonadError e m)
    => Program tyname name uni fun ann -> m ()
checkProgram (Program _ _ t) = checkTerm t

-- | Ensure that all types in the 'Term' are normalized.
checkTerm
    :: (AsNormCheckError e tyname name uni fun ann, MonadError e m)
    => Term tyname name uni fun ann -> m ()
checkTerm p = throwingEither _NormCheckError $ check p

check :: Term tyname name uni fun ann -> Either (NormCheckError tyname name uni fun ann) ()
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

isNormalType :: Type tyname uni ann -> Bool
isNormalType = isRight . normalType

normalType :: Type tyname uni ann -> Either (NormCheckError tyname name uni fun ann) ()
normalType (TyFun _ i o)       = normalType i >> normalType o
normalType (TyForall _ _ _ ty) = normalType ty
normalType (TyIFix _ pat arg)  = normalType pat >> normalType arg
normalType (TyLam _ _ _ ty)    = normalType ty
-- See Note [PLC types and universes].
normalType TyBuiltin{}         = pure ()
normalType ty                  = neutralType ty

neutralType :: Type tyname uni ann -> Either (NormCheckError tyname name uni fun ann) ()
neutralType TyVar{}           = pure ()
neutralType (TyApp _ ty1 ty2) = neutralType ty1 >> normalType ty2
neutralType ty                = Left (BadType (toAnnotation ty) ty "neutral type")
