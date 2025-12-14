{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}

-- | This module makes sure types are normalized inside programs.
module PlutusCore.Check.Normal
  ( checkProgram
  , checkTerm
  , isNormalType
  , NormCheckError (..)
  ) where

import PlutusPrelude

import PlutusCore.Core
import PlutusCore.Error
import PlutusCore.MkPlc (mkTyBuiltinOf)

import Control.Monad.Except
import Universe.Core (HasUniApply (matchUniApply), SomeTypeIn (..))

-- | Ensure that all types in the 'Program' are normalized.
checkProgram
  :: (HasUniApply uni, MonadError (NormCheckError tyname name uni fun ann) m)
  => Program tyname name uni fun ann -> m ()
checkProgram (Program _ _ t) = checkTerm t

-- | Ensure that all types in the 'Term' are normalized.
checkTerm
  :: (HasUniApply uni, MonadError (NormCheckError tyname name uni fun ann) m)
  => Term tyname name uni fun ann -> m ()
checkTerm p = liftEither $ check p

check
  :: HasUniApply uni
  => Term tyname name uni fun ann -> Either (NormCheckError tyname name uni fun ann) ()
check (Error _ ty) = normalType ty
check (TyInst _ t ty) = check t >> normalType ty
check (IWrap _ pat arg term) = normalType pat >> normalType arg >> check term
check (Unwrap _ t) = check t
check (LamAbs _ _ ty t) = normalType ty >> check t
check (Apply _ t1 t2) = check t1 >> check t2
check (TyAbs _ _ _ t) = check t
check (Constr _ ty _ es) = normalType ty >> traverse_ check es
check (Case _ ty arg cs) = normalType ty >> check arg >> traverse_ check cs
check Var {} = pure ()
check Constant {} = pure ()
check Builtin {} = pure ()

isNormalType :: HasUniApply uni => Type tyname uni ann -> Bool
isNormalType = isRight . normalType

normalType
  :: HasUniApply uni
  => Type tyname uni ann -> Either (NormCheckError tyname name uni fun ann) ()
normalType (TyFun _ i o) = normalType i >> normalType o
normalType (TyForall _ _ _ ty) = normalType ty
normalType (TyIFix _ pat arg) = normalType pat >> normalType arg
normalType (TySOP _ tyls) = traverse_ (traverse_ normalType) tyls
normalType (TyLam _ _ _ ty) = normalType ty
normalType ty = neutralType ty

neutralType
  :: HasUniApply uni
  => Type tyname uni ann -> Either (NormCheckError tyname name uni fun ann) ()
neutralType TyVar {} = pure ()
neutralType (TyBuiltin ann someUni) = neutralUni ann someUni
neutralType (TyApp _ ty1 ty2) = neutralType ty1 >> normalType ty2
neutralType ty = Left (BadType (typeAnn ty) ty "neutral type")

-- See Note [Normalization of built-in types].
neutralUni
  :: HasUniApply uni
  => ann -> SomeTypeIn uni -> Either (NormCheckError tyname name uni fun ann) ()
neutralUni ann (SomeTypeIn uni) =
  matchUniApply
    uni
    -- If @uni@ is not an intra-universe application, then it's neutral.
    (Right ())
    -- If it is, then it's not neutral and we throw an error.
    (\_ _ -> Left (BadType ann (mkTyBuiltinOf ann uni) "neutral type"))
