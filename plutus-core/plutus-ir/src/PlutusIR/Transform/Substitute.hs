{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ViewPatterns     #-}
-- | Implements naive substitution functions for replacing type and term variables.
module PlutusIR.Transform.Substitute (
      substVar
    , substTyVar
    , typeSubstTyNames
    , termSubstNames
    , termSubstTyNames
    , bindingSubstNames
    , bindingSubstTyNames
    ) where

import           PlutusIR

import           PlutusCore.Subst (substTyVar, typeSubstTyNames)

import           Control.Lens

import           Data.Maybe

-- Needs to be different from the PLC version since we have different Terms
-- | Replace a variable using the given function.
substVar :: (name -> Maybe (Term tyname name uni fun a)) -> Term tyname name uni fun a -> Maybe (Term tyname name uni fun a)
substVar nameF (Var _ n) = nameF n
substVar _     _         = Nothing

-- | Naively substitute names using the given functions (i.e. do not substitute binders).
termSubstNames :: (name -> Maybe (Term tyname name uni fun a)) -> Term tyname name uni fun a -> Term tyname name uni fun a
termSubstNames nameF = transformOf termSubterms (\x -> fromMaybe x (substVar nameF x))

-- | Naively substitute type names using the given functions (i.e. do not substitute binders).
termSubstTyNames :: (tyname -> Maybe (Type tyname uni a)) -> Term tyname name uni fun a -> Term tyname name uni fun a
termSubstTyNames tynameF = over termSubterms (termSubstTyNames tynameF) . over termSubtypes (typeSubstTyNames tynameF)

-- | Naively substitute names using the given functions (i.e. do not substitute binders).
bindingSubstNames :: (name -> Maybe (Term tyname name uni fun a)) -> Binding tyname name uni fun a -> Binding tyname name uni fun a
bindingSubstNames nameF = over bindingSubterms (termSubstNames nameF)

-- | Naively substitute type names using the given functions (i.e. do not substitute binders).
bindingSubstTyNames :: (tyname -> Maybe (Type tyname uni a)) -> Binding tyname name uni fun a -> Binding tyname name uni fun a
bindingSubstTyNames tynameF = over bindingSubterms (termSubstTyNames tynameF) . over bindingSubtypes (typeSubstTyNames tynameF)
