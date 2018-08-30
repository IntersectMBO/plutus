{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE TypeFamilies          #-}

-- | This module makes sure terms and types are well-formed according to Fig. 2
module Language.PlutusCore.Normalize ( check
                                     , NormalizationError
                                     ) where

import           Data.Functor.Foldable
import           Data.Functor.Foldable.Monadic
import           Language.PlutusCore.PrettyCfg
import           Language.PlutusCore.Type
import           PlutusPrelude

data NormalizationError a = BadType a
                          | BadTerm a
                          deriving (Generic, NFData)

instance PrettyCfg a => PrettyCfg (NormalizationError a) where
    prettyCfg cfg (BadType l) = "Malformed type at" <+> prettyCfg cfg l
    prettyCfg cfg (BadTerm l) = "Malformed term at" <+> prettyCfg cfg l

check :: Program tyname name a -> Maybe (NormalizationError a)
check = go . preCheck where
    go Right{}  = Nothing
    go (Left x) = Just x

-- | Ensure that all terms and types are well-formed accoring to Fig. 2
preCheck :: Program tyname name a -> Either (NormalizationError a) (Program tyname name a)
preCheck (Program l v t) = Program l v <$> checkTerm t

-- this basically ensures all type instatiations, etc. occur only with type *values*
checkTerm :: Term tyname name a -> Either (NormalizationError a) (Term tyname name a)
checkTerm (Error l ty)      = Error l <$> typeValue ty
checkTerm (TyInst l t ty)   = TyInst l <$> checkTerm t <*> typeValue ty
checkTerm (Wrap l tn ty t)  = Wrap l tn <$> typeValue ty <*> checkTerm t
checkTerm (Unwrap l t)      = Unwrap l <$> checkTerm t
checkTerm (LamAbs l n ty t) = LamAbs l n <$> typeValue ty <*> checkTerm t
checkTerm (Apply l t t')    = Apply l <$> checkTerm t <*> checkTerm t'
checkTerm (TyAbs l tn k t)  = TyAbs l tn k <$> termValue t
checkTerm t@Var{}           = pure t
checkTerm t@Constant{}      = pure t

-- ensure a term is a value
termValue :: Term tyname name a -> Either (NormalizationError a) (Term tyname name a)
termValue t@Constant{}      = pure t
termValue (LamAbs l n ty t) = LamAbs l n <$> typeValue ty <*> checkTerm t
termValue (Wrap l tn ty t)  = Wrap l tn <$> typeValue ty <*> termValue t
termValue (TyAbs l tn k t)  = TyAbs l tn k <$> termValue t
termValue t                 = Left (BadTerm (termLoc t))

-- ensure that a type is a type value
typeValue :: Type tyname a -> Either (NormalizationError a) (Type tyname a)
typeValue = cataM aM where

    aM ty | isTyValue ty = pure (embed ty)
          | otherwise    = neutralType (embed ty)

    isTyValue TyFunF{}     = True
    isTyValue TyForallF{}  = True
    isTyValue TyFixF{}     = True
    isTyValue TyLamF{}     = True
    isTyValue TyBuiltinF{} = True
    isTyValue _            = False

-- ensure a type is a neutral type
neutralType :: Type tyname a -> Either (NormalizationError a) (Type tyname a)
neutralType = cataM aM where

    aM ty | isNeutralType ty = pure (embed ty)
          | otherwise        = Left (BadType (tyLocF ty))

    isNeutralType TyVarF{} = True
    isNeutralType TyAppF{} = True
    isNeutralType _        = False

    tyLocF = tyLoc . embed
