{-# LANGUAGE FlexibleContexts #-}

-- | Implements naive substitution functions for replacing type and term variables.
module PlutusIR.Transform.Substitute (
  substVarA,
  substTyVarA,
  typeSubstTyNames,
  termSubstNames,
  termSubstNamesM,
  termSubstTyNames,
  termSubstTyNamesM,
  bindingSubstNames,
  bindingSubstTyNames,
) where

import PlutusCore.Subst (purely, typeSubstTyNames)
import PlutusIR
import PlutusPrelude

import Control.Lens

{-# INLINE substVarA #-}
-- | Applicatively replace a variable using the given function.
substVarA ::
  (Applicative f) =>
  (name -> f (Maybe (Term tyname name uni fun ann))) ->
  Term tyname name uni fun ann ->
  f (Term tyname name uni fun ann)
substVarA nameF t@(Var _ name) = fromMaybe t <$> nameF name
substVarA _ t                  = pure t

{-# INLINE substTyVarA #-}
-- | Applicatively replace a type variable using the given function.
substTyVarA ::
  (Applicative f) =>
  (tyname -> f (Maybe (Type tyname uni ann))) ->
  Type tyname uni ann ->
  f (Type tyname uni ann)
substTyVarA tynameF ty@(TyVar _ tyname) = fromMaybe ty <$> tynameF tyname
substTyVarA _ ty                        = pure ty

-- | Naively substitute names using the given functions (i.e. do not substitute binders).
termSubstNames ::
  (name -> Maybe (Term tyname name uni fun a)) ->
  Term tyname name uni fun a ->
  Term tyname name uni fun a
termSubstNames = purely termSubstNamesM

-- | Naively monadically substitute names using the given function (i.e. do not substitute binders).
termSubstNamesM ::
  (Monad m) =>
  (name -> m (Maybe (Term tyname name uni fun ann))) ->
  Term tyname name uni fun ann ->
  m (Term tyname name uni fun ann)
termSubstNamesM = transformMOf termSubterms . substVarA

-- | Naively substitute type names using the given functions (i.e. do not substitute binders).
termSubstTyNames ::
  (tyname -> Maybe (Type tyname uni a)) ->
  Term tyname name uni fun a ->
  Term tyname name uni fun a
termSubstTyNames = purely termSubstTyNamesM

{- | Naively monadically substitute type names using the given function
(i.e. do not substitute binders).
-}
termSubstTyNamesM ::
  (Monad m) =>
  (tyname -> m (Maybe (Type tyname uni ann))) ->
  Term tyname name uni fun ann ->
  m (Term tyname name uni fun ann)
termSubstTyNamesM =
  transformMOf termSubterms . traverseOf termSubtypes . transformMOf typeSubtypes . substTyVarA

-- | Naively substitute names using the given functions (i.e. do not substitute binders).
bindingSubstNames ::
  (name -> Maybe (Term tyname name uni fun a)) ->
  Binding tyname name uni fun a ->
  Binding tyname name uni fun a
bindingSubstNames nameF = over bindingSubterms (termSubstNames nameF)

-- | Naively substitute type names using the given functions (i.e. do not substitute binders).
bindingSubstTyNames ::
  (tyname -> Maybe (Type tyname uni a)) ->
  Binding tyname name uni fun a ->
  Binding tyname name uni fun a
bindingSubstTyNames tynameF =
  over bindingSubterms (termSubstTyNames tynameF)
    . over bindingSubtypes (typeSubstTyNames tynameF)
