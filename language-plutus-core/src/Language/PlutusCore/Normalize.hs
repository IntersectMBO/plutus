{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE TypeFamilies          #-}

-- | This module makes sure terms and types are well-formed according to Fig. 2
module Language.PlutusCore.Normalize ( normalize
                                     , NormalizationError (..)
                                     ) where

import           Data.Functor.Foldable
import           Data.Functor.Foldable.Monadic
import           Language.PlutusCore.Type
import           PlutusPrelude

data NormalizationError a = BadType a
                          | BadTerm a

instance Pretty a => Pretty (NormalizationError a) where
    pretty (BadType l) = "Malformed type at" <+> pretty l
    pretty (BadTerm l) = "Malformed term at" <+> pretty l

normalize :: Program tyname name a -> Either (NormalizationError a) (Program tyname name a)
normalize (Program l v t) = Program l v <$> normalizeTerm t

-- this basically ensures all type instatiations, etc. occur only with type *values*
normalizeTerm :: Term tyname name a -> Either (NormalizationError a) (Term tyname name a)

normalizeTerm (Error l ty)      = Error l <$> typeValue ty
normalizeTerm (TyInst l t ty)   = TyInst l <$> normalizeTerm t <*> typeValue ty
normalizeTerm (Wrap l tn ty t)  = Wrap l tn <$> typeValue ty <*> normalizeTerm t
normalizeTerm (Unwrap l t)      = Unwrap l <$> normalizeTerm t
normalizeTerm (LamAbs l n ty t) = LamAbs l n <$> typeValue ty <*> normalizeTerm t
normalizeTerm (Apply l t t')    = Apply l <$> normalizeTerm t <*> normalizeTerm t'
normalizeTerm (TyAbs l tn k t)  = TyAbs l tn k <$> termValue t
normalizeTerm t@Var{}           = pure t
normalizeTerm t@Constant{}      = pure t

-- ensure a term is a value
termValue :: Term tyname name a -> Either (NormalizationError a) (Term tyname name a)
termValue t@Constant{}      = pure t
termValue (LamAbs l n ty t) = LamAbs l n <$> typeValue ty <*> normalizeTerm t
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
