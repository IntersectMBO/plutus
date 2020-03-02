{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ViewPatterns     #-}
-- | Implements naive substitution functions for replacing type and term variables.
module Language.PlutusIR.Transform.Substitute (
      substVar
    , substTyVar
    , typeSubstTyNames
    , termSubstNames
    , termSubstTyNames
    , bindingSubstNames
    , bindingSubstTyNames
    ) where

import           Language.PlutusIR

import           Language.PlutusCore.Subst (substTyVar, typeSubstTyNames)

import           Control.Lens

-- Needs to be different from the PLC version since we have different Terms
-- | Replace a variable using the given function.
substVar :: (name a -> Maybe (Term tyname name uni a)) -> Term tyname name uni a -> Term tyname name uni a
substVar nameF (Var _ (nameF -> Just t)) = t
substVar _ t                             = t

-- | Naively substitute names using the given functions (i.e. do not substitute binders).
termSubstNames :: (name a -> Maybe (Term tyname name uni a)) -> Term tyname name uni a -> Term tyname name uni a
termSubstNames nameF = transformOf termSubterms (substVar nameF)

-- | Naively substitute type names using the given functions (i.e. do not substitute binders).
termSubstTyNames :: (tyname a -> Maybe (Type tyname uni a)) -> Term tyname name uni a -> Term tyname name uni a
termSubstTyNames tynameF = over termSubterms (termSubstTyNames tynameF) . over termSubtypes (typeSubstTyNames tynameF)

-- | Naively substitute names using the given functions (i.e. do not substitute binders).
bindingSubstNames :: (name a -> Maybe (Term tyname name uni a)) -> Binding tyname name uni a -> Binding tyname name uni a
bindingSubstNames nameF = over bindingSubterms (termSubstNames nameF)

-- | Naively substitute type names using the given functions (i.e. do not substitute binders).
bindingSubstTyNames :: (tyname a -> Maybe (Type tyname uni a)) -> Binding tyname name uni a -> Binding tyname name uni a
bindingSubstTyNames tynameF = over bindingSubterms (termSubstTyNames tynameF) . over bindingSubtypes (typeSubstTyNames tynameF)
