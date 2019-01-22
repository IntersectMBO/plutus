module Language.PlutusCore.Subst(
                                  substTerm
                                , substTy
                                , fvTerm
                                , ftvTerm
                                , ftvTy
                                ) where

import           Language.PlutusCore.Type
import           PlutusPrelude            hiding (empty)

import           Data.Functor.Foldable    (cata, project)
import           Data.Set

-- | Naively substitute names using the given functions (i.e. do not account for scoping).
substTerm ::
  (tyname a -> Maybe (Type tyname a)) ->
  (name a -> Maybe (Term tyname name a)) ->
  Term tyname name a ->
  Term tyname name a
substTerm tynameF nameF = hoist f
  where
    f (VarF a bnd)         = case nameF bnd of
      Just t  -> project t
      Nothing -> VarF a bnd
    f (LamAbsF a bnd ty t)  = LamAbsF a bnd (substTy tynameF ty) t
    f (TyInstF a t ty)      = TyInstF a t (substTy tynameF ty)
    f (IWrapF a pat arg t)  = IWrapF a (substTy tynameF pat) (substTy tynameF arg) t
    f (ErrorF a ty)         = ErrorF a (substTy tynameF ty)
    f x                     = x

-- | Naively substitute names using the given function (i.e. do not account for scoping).
substTy ::
  (tyname a -> Maybe (Type tyname a)) ->
  Type tyname a ->
  Type tyname a
substTy tynameF = hoist f
  where
    f (TyVarF a ty) = case tynameF ty of
       Just t  -> project t
       Nothing -> TyVarF a ty
    f x           = x

-- Free variables

-- | Get all the free term variables in a term.
fvTerm :: (Ord (name a)) => Term tyname name a -> Set (name a)
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
ftvTerm :: (Ord (tyname a)) => Term tyname name a -> Set (tyname a)
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
ftvTy :: (Ord (tyname a)) => Type tyname a -> Set (tyname a)
ftvTy = cata f
  where
    f (TyVarF _ ty)          = singleton ty
    f (TyFunF _ i o)         = i `union` o
    f (TyIFixF _ pat arg)    = pat `union` arg
    f (TyForallF _ bnd _ ty) = delete bnd ty
    f (TyLamF _ bnd _ ty)    = delete bnd ty
    f (TyAppF _ ty1 ty2)     = ty1 `union` ty2
    f _                      = empty
