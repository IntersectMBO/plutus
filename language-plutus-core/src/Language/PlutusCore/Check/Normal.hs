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

import           Language.PlutusCore.Error
import           Language.PlutusCore.Name
import           Language.PlutusCore.Type
import           PlutusPrelude

-- | Ensure that all types in the 'Program' are normalized.
checkProgram :: (AsNormalizationError e TyName Name a, MonadError e m) => Program TyName Name a -> m ()
checkProgram (Program _ _ t) = checkTerm t

-- | Ensure that all types in the 'Term' are normalized.
checkTerm :: (AsNormalizationError e TyName Name a, MonadError e m) => Term TyName Name a -> m ()
checkTerm p = throwingEither _NormalizationError $ check p

check :: Term tyname name a -> Either (NormalizationError tyname name a) ()
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

isNormalType :: Type tyname a -> Bool
isNormalType = isRight . normalType

normalType :: Type tyname a -> Either (NormalizationError tyname name a) ()
normalType (TyFun _ i o)       = normalType i >> normalType o
normalType (TyForall _ _ _ ty) = normalType ty
normalType (TyIFix _ pat arg)  = normalType pat >> normalType arg
normalType (TyLam _ _ _ ty)    = normalType ty
normalType ty                  = neutralType ty

neutralType :: Type tyname a -> Either (NormalizationError tyname name a) ()
neutralType TyVar{}           = pure ()
neutralType (TyApp _ ty1 ty2) = neutralType ty1 >> normalType ty2
-- See note [Builtin applications and values]
neutralType TyBuiltin{}       = pure ()
neutralType ty                = Left (BadType (tyLoc ty) ty "neutral type")
