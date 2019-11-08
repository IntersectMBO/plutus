{-# LANGUAGE ViewPatterns #-}
module Language.PlutusCore.Subst
    ( termSubstNames
    , termSubstTyNames
    , typeSubstTyNames
    , substTyVar
    , substVar
    , fvTerm
    , ftvTerm
    , ftvTy
    ) where

import           Control.Lens
import           Language.PlutusCore.Type

import           Data.Functor.Foldable    (cata)
import           Data.Set

-- | Replace a type variable using the given function.
substTyVar
    :: (tyname ann -> Maybe (Type tyname ann))
    -> Type tyname ann
    -> Type tyname ann
substTyVar tynameF (TyVar _ (tynameF -> Just t)) = t
substTyVar _       t                             = t

-- | Replace a variable using the given function.
substVar
    :: (name ann -> Maybe (Term tyname name ann))
    -> Term tyname name ann
    -> Term tyname name ann
substVar nameF (Var _ (nameF -> Just t)) = t
substVar _     t                         = t

-- | Naively substitute type names (i.e. do not substitute binders).
typeSubstTyNames
    :: (tyname ann -> Maybe (Type tyname ann))
    -> Type tyname ann
    -> Type tyname ann
typeSubstTyNames tynameF = transformOf typeSubtypes (substTyVar tynameF)

-- | Naively substitute names using the given functions (i.e. do not substitute binders).
termSubstNames
    :: (name ann -> Maybe (Term tyname name ann))
    -> Term tyname name ann
    -> Term tyname name ann
termSubstNames nameF = transformOf termSubterms (substVar nameF)

-- | Naively substitute type names using the given functions (i.e. do not substitute binders).
termSubstTyNames
    :: (tyname ann -> Maybe (Type tyname ann))
    -> Term tyname name ann
    -> Term tyname name ann
termSubstTyNames tynameF =
    over termSubterms (termSubstTyNames tynameF) . over termSubtypes (typeSubstTyNames tynameF)

-- Free variables

-- | Get all the free term variables in a term.
fvTerm :: Ord (name ann) => Term tyname name ann -> Set (name ann)
fvTerm = cata f
  where
    f (VarF _ n)        = singleton n
    f (TyAbsF _ _ _ t)  = t
    f (LamAbsF _ n _ t) = delete n t
    f (ApplyF _ t1 t2)  = t1 `union` t2
    f (TyInstF _ t _)   = t
    f (UnwrapF _ t)     = t
    f (IWrapF _ _ _ t)  = t
    f _                 = empty

-- | Get all the free type variables in a term.
ftvTerm :: Ord (tyname ann) => Term tyname name ann -> Set (tyname ann)
ftvTerm = cata f
  where
    f (TyAbsF _ ty _ t)    = delete ty t
    f (LamAbsF _ _ ty t)   = ftvTy ty `union` t
    f (ApplyF _ t1 t2)     = t1 `union` t2
    f (TyInstF _ t ty)     = t `union` ftvTy ty
    f (UnwrapF _ t)        = t
    f (IWrapF _ pat arg t) = ftvTy pat `union` ftvTy arg `union` t
    f _                    = empty

-- | Get all the free type variables in a type.
ftvTy :: Ord (tyname ann) => Type tyname ann -> Set (tyname ann)
ftvTy = cata f
  where
    f (TyVarF _ ty)          = singleton ty
    f (TyFunF _ i o)         = i `union` o
    f (TyIFixF _ pat arg)    = pat `union` arg
    f (TyForallF _ bnd _ ty) = delete bnd ty
    f (TyLamF _ bnd _ ty)    = delete bnd ty
    f (TyAppF _ ty1 ty2)     = ty1 `union` ty2
    f _                      = empty
