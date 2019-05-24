{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ViewPatterns     #-}
-- | Implements naive substitution functions for replacing type and term variables.
module Language.PlutusIR.Transform.Substitute (
      typeSubstTyNames
    , termSubstNames
    , termSubstTyNames
    , bindingSubstNames
    , bindingSubstTyNames
    ) where

import           Language.PlutusIR

import           Control.Lens

-- | Replace a type variable using the given function.
substTyVar :: (tyname a -> Maybe (Type tyname a)) -> Type tyname a -> Type tyname a
substTyVar tynameF (TyVar _ (tynameF -> Just t)) = t
substTyVar _ t                                   = t

-- | Replace a variable using the given function.
substVar :: (name a -> Maybe (Term tyname name a)) -> Term tyname name a -> Term tyname name a
substVar nameF (Var _ (nameF -> Just t)) = t
substVar _ t                             = t

-- | Naively substitute type names (i.e. do not substitute binders).
typeSubstTyNames :: (tyname a -> Maybe (Type tyname a)) -> Type tyname a -> Type tyname a
typeSubstTyNames tynameF = transformOf typeSubtypes (substTyVar tynameF)

-- | Naively substitute names using the given functions (i.e. do not substitute binders).
termSubstNames :: (name a -> Maybe (Term tyname name a)) -> Term tyname name a -> Term tyname name a
termSubstNames nameF = transformOf termSubterms (substVar nameF)

-- | Naively substitute type names using the given functions (i.e. do not substitute binders).
termSubstTyNames :: (tyname a -> Maybe (Type tyname a)) -> Term tyname name a -> Term tyname name a
termSubstTyNames tynameF = over termSubterms (termSubstTyNames tynameF) . over termSubtypes (typeSubstTyNames tynameF)

-- | Naively substitute names using the given functions (i.e. do not substitute binders).
bindingSubstNames :: (name a -> Maybe (Term tyname name a)) -> Binding tyname name a -> Binding tyname name a
bindingSubstNames nameF = over bindingSubterms (termSubstNames nameF)

-- | Naively substitute type names using the given functions (i.e. do not substitute binders).
bindingSubstTyNames :: (tyname a -> Maybe (Type tyname a)) -> Binding tyname name a -> Binding tyname name a
bindingSubstTyNames tynameF = over bindingSubterms (termSubstTyNames tynameF) . over bindingSubtypes (typeSubstTyNames tynameF)
