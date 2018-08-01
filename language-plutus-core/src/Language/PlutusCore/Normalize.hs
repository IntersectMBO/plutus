{-# LANGUAGE TypeFamilies #-}

-- | This module makes sure terms and types are well-formed according to Fig. 2
module Language.PlutusCore.Normalize ( normalize
                                     ) where

import           Data.Functor.Foldable
import           Data.Functor.Foldable.Monadic
import           Language.PlutusCore.Type

data NormalizationError = BadType

normalize :: Program tyname name a -> Either NormalizationError (Program tyname name a)
normalize (Program l v t) = Program l v <$> normalizeTerm t

-- this basically ensures all type instatiations, etc. occur only with type *values*
normalizeTerm :: Term tyname name a -> Either NormalizationError (Term tyname name a)
normalizeTerm (Error l ty)      = Error l <$> typeValue ty
normalizeTerm (TyInst l t ty)   = TyInst l <$> normalizeTerm t <*> typeValue ty
normalizeTerm (Wrap l tn ty t)  = Wrap l tn <$> typeValue ty <*> normalizeTerm t
normalizeTerm (Unwrap l t)      = Unwrap l <$> normalizeTerm t
normalizeTerm (LamAbs l n ty t) = LamAbs l n <$> typeValue ty <*> normalizeTerm t
normalizeTerm (Apply l t t')    = Apply l <$> normalizeTerm t <*> normalizeTerm t'
normalizeTerm t@Var{}           = pure t
normalizeTerm t@Constant{}      = pure t

typeValue :: Type tyname a -> Either NormalizationError (Type tyname a)
typeValue = cataM aM where

    aM ty | isTyValue ty = pure (embed ty)
          | otherwise    = neutralType (embed ty)

    isTyValue TyFunF{}     = True
    isTyValue TyForallF{}  = True
    isTyValue TyFixF{}     = True
    isTyValue TyLamF{}     = True
    isTyValue TyBuiltinF{} = True
    isTyValue _            = False

neutralType :: Type tyname a -> Either NormalizationError (Type tyname a)
neutralType = cataM aM where

    aM ty | isNeutralType ty = pure (embed ty)
          | otherwise        = Left BadType

    isNeutralType TyVarF{} = True
    isNeutralType TyAppF{} = True
    isNeutralType _        = False
