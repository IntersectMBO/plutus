module Language.PlutusCore.Core.Variables
    ( fvTerm
    , ftvTerm
    , ftvTy
    , fuTerm
    , ftuTerm
    , ftuTy
    , vTerm
    , tvTerm
    , tvTy
    , uniquesType
    , uniquesTerm
    ) where

import           Language.PlutusCore.Core.Instance.Recursive
import           Language.PlutusCore.Core.Plated
import           Language.PlutusCore.Core.Type
import           Language.PlutusCore.Name

import           Control.Lens
import           Data.Functor.Foldable                       (cata)
import           Data.Set                                    as Set

-- Free variables

-- | Get all the free term variables in a term.
fvTerm :: Ord name => Term tyname name uni fun ann -> Set name
fvTerm = cata f
  where
    f (VarF _ n)        = singleton n
    f (TyAbsF _ _ _ t)  = t
    f (LamAbsF _ n _ t) = delete n t
    f (ApplyF _ t1 t2)  = t1 `union` t2
    f (TyInstF _ t _)   = t
    f (UnwrapF _ t)     = t
    f (IWrapF _ _ _ t)  = t
    f ConstantF{}       = Set.empty
    f BuiltinF{}        = Set.empty
    f ErrorF{}          = Set.empty

-- | Get all the free type variables in a term.
ftvTerm :: Ord tyname => Term tyname name uni fun ann -> Set tyname
ftvTerm = cata f
  where
    f (TyAbsF _ ty _ t)    = delete ty t
    f (LamAbsF _ _ ty t)   = ftvTy ty `union` t
    f (ApplyF _ t1 t2)     = t1 `union` t2
    f (TyInstF _ t ty)     = t `union` ftvTy ty
    f (UnwrapF _ t)        = t
    f (IWrapF _ pat arg t) = ftvTy pat `union` ftvTy arg `union` t
    f (ErrorF _ ty)        = ftvTy ty
    f VarF{}               = Set.empty
    f ConstantF{}          = Set.empty
    f BuiltinF{}           = Set.empty

-- | Get all the free type variables in a type.
ftvTy :: Ord tyname => Type tyname uni ann -> Set tyname
ftvTy = cata f
  where
    f (TyVarF _ ty)          = singleton ty
    f (TyFunF _ i o)         = i `union` o
    f (TyIFixF _ pat arg)    = pat `union` arg
    f (TyForallF _ bnd _ ty) = delete bnd ty
    f (TyLamF _ bnd _ ty)    = delete bnd ty
    f (TyAppF _ ty1 ty2)     = ty1 `union` ty2
    f TyBuiltinF{}           = Set.empty

-- Free uniques

-- | Get all the free term variables in a term.
fuTerm :: HasUnique name TermUnique => Term tyname name uni fun ann -> Set TermUnique
fuTerm = cata f
  where
    f (VarF _ n)        = singleton $ n ^. unique
    f (TyAbsF _ _ _ t)  = t
    f (LamAbsF _ n _ t) = delete (n ^. unique) t
    f (ApplyF _ t1 t2)  = t1 `union` t2
    f (TyInstF _ t _)   = t
    f (UnwrapF _ t)     = t
    f (IWrapF _ _ _ t)  = t
    f ConstantF{}       = Set.empty
    f BuiltinF{}        = Set.empty
    f ErrorF{}          = Set.empty

-- | Get all the free type variables in a term.
ftuTerm :: HasUnique tyname TypeUnique => Term tyname name uni fun ann -> Set TypeUnique
ftuTerm = cata f
  where
    f (TyAbsF _ ty _ t)    = delete (ty ^. unique) t
    f (LamAbsF _ _ ty t)   = ftuTy ty `union` t
    f (ApplyF _ t1 t2)     = t1 `union` t2
    f (TyInstF _ t ty)     = t `union` ftuTy ty
    f (UnwrapF _ t)        = t
    f (IWrapF _ pat arg t) = ftuTy pat `union` ftuTy arg `union` t
    f (ErrorF _ ty)        = ftuTy ty
    f VarF{}               = Set.empty
    f ConstantF{}          = Set.empty
    f BuiltinF{}           = Set.empty

-- | Get the uniques of all the free type variables in a type.
ftuTy :: HasUnique tyname TypeUnique => Type tyname uni ann -> Set TypeUnique
ftuTy = cata f
  where
    f (TyVarF _ ty)          = singleton $ ty ^. unique
    f (TyFunF _ i o)         = i `union` o
    f (TyIFixF _ pat arg)    = pat `union` arg
    f (TyForallF _ bnd _ ty) = delete (bnd ^. unique) ty
    f (TyLamF _ bnd _ ty)    = delete (bnd ^. unique) ty
    f (TyAppF _ ty1 ty2)     = ty1 `union` ty2
    f TyBuiltinF{}           = Set.empty

-- All variables

setOf :: Getting (Set a) s a -> s -> Set a
setOf g = foldMapOf g singleton

-- | Get all the term variables in a term.
vTerm :: Ord name => Term tyname name uni fun ann -> Set name
vTerm = setOf $ termSubtermsDeep . termVars

-- | Get all the type variables in a term.
tvTerm :: Ord tyname => Term tyname name uni fun ann -> Set tyname
tvTerm = setOf $ termSubtypesDeep . typeTyVars

-- | Get all the type variables in a type.
tvTy :: Ord tyname => Type tyname uni ann -> Set tyname
tvTy = setOf $ typeSubtypesDeep . typeTyVars

-- All uniques

-- | Get all the uniques in a type.
uniquesType :: HasUniques (Type tyname uni ann) => Type tyname uni ann -> Set Unique
uniquesType = setOf typeUniquesDeep

-- | Get all the uniques in a term (including the type-level ones).
uniquesTerm :: HasUniques (Term tyname name uni fun ann) => Term tyname name uni fun ann -> Set Unique
uniquesTerm = setOf termUniquesDeep
