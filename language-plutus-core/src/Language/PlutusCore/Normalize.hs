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

-- this basically ensures all type instatiations occur only with type *values*
normalizeTerm :: Term tyname name a -> Either NormalizationError (Term tyname name a)
normalizeTerm (Error l ty)    = Error l <$> typeValue ty
normalizeTerm (TyInst l t ty) = TyInst l t <$> typeValue ty
normalizeTerm x               = pure x

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
