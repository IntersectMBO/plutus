module Language.PlutusCore.Subst(
                                  captureAvoidingSubstTerm
                                , captureAvoidingSubstTy
                                , substTerm
                                , substTy
                                , fvTerm
                                , ftvTerm
                                , ftvTy
                                ) where

import           PlutusPrelude hiding (empty)
import           Language.PlutusCore

import           Control.Monad
import           Data.Functor.Foldable
import           Data.Set

{--
When we substitute in a term, we can't just splice in the AST, because it might have overlapping names.

We resolve this by "upshifting" the unique counters of all the names in the term being substituted, so that
they're guaranteed not to overlap with those in the term being substituted into.
--}

-- TODO: make nicer with lenses or something

getNameUnique :: Name a -> Int
getNameUnique = unUnique . nameUnique

getTyNameUnique :: TyName a -> Int
getTyNameUnique = getNameUnique . unTyName

incNameUnique :: Int -> Name a -> Name a
incNameUnique i n = n { nameUnique = (nameUnique n) { unUnique = ((getNameUnique n) + i) }}

incTyNameUnique :: Int -> TyName a -> TyName a
incTyNameUnique i n = n { unTyName = (incNameUnique i (unTyName n)) }

incTermUniques :: Int -> Term TyName Name a -> Term TyName Name a
incTermUniques i = mapNamesTerm (incTyNameUnique i) (incNameUnique i)

incTypeUniques :: Int -> Type TyName a -> Type TyName a
incTypeUniques i = mapNamesTy (incTyNameUnique i)

-- | Get the maximum unique in a term.
maxUniqueTerm :: Term TyName Name a -> Int
maxUniqueTerm = cata f
  where
    f(VarF _ n)         = getNameUnique n
    f(TyAbsF _ n _ t)   = max (getTyNameUnique n) t
    f(LamAbsF _ n ty t) = max (getNameUnique n) (max (maxUniqueTy ty) t)
    f(ApplyF _ t1 t2)   = max t1 t2
    f(TyInstF _ t ty)   = max t (maxUniqueTy ty)
    f(UnwrapF _ t)      = t
    f(WrapF _ n ty t)   = max (getTyNameUnique n) (max (maxUniqueTy ty) t)
    f(ErrorF _ ty)      = maxUniqueTy ty
    f(_)                = 0

-- | Get the maximum unique in a type.
maxUniqueTy :: Type TyName a -> Int
maxUniqueTy = cata f
  where
    f(TyVarF _ ty)          = getTyNameUnique ty
    f(TyFunF _ i o)         = max i o
    f(TyFixF _ bnd ty)      = max (getTyNameUnique bnd) ty
    f(TyForallF _ bnd _ ty) = max (getTyNameUnique bnd) ty
    f(TyLamF _ bnd _ ty)    = max (getTyNameUnique bnd) ty
    f(TyAppF _ ty1 ty2)     = max ty1 ty2
    f(_)                    = 0

-- | Apply the given functions to all the names in a term.
mapNamesTerm ::
  (tyname a -> tyname a) ->
  (name a -> name a) ->
  Term tyname name a ->
  Term tyname name a
mapNamesTerm tynameF nameF = hoist f
  where
    f(VarF a bnd)         = VarF a (nameF bnd)
    f(TyAbsF a bnd k t)   = TyAbsF a (tynameF bnd) k t
    f(LamAbsF a bnd ty t) = LamAbsF a (nameF bnd) (mapNamesTy tynameF ty) t
    f(TyInstF a t ty)     = TyInstF a t (mapNamesTy tynameF ty)
    f(WrapF a bnd ty t)   = WrapF a (tynameF bnd) (mapNamesTy tynameF ty) t
    f(ErrorF a ty)        = ErrorF a (mapNamesTy tynameF ty)
    f(x)                  = x

-- | Apply the given function to all the names in a type.
mapNamesTy ::
  (tyname a -> tyname a) ->
  Type tyname a ->
  Type tyname a
mapNamesTy tynameF = hoist f
  where
    f(TyVarF a ty)          = TyVarF a (tynameF ty)
    f(TyFixF a bnd ty)      = TyFixF a (tynameF bnd) ty
    f(TyForallF a bnd k ty) = TyForallF a (tynameF bnd) k ty
    f(TyLamF a bnd k ty)    = TyLamF a (tynameF bnd) k ty
    f(x)                    = x

-- | Naively substitute names using the given functions (i.e. do not account for scoping).
substTerm ::
  (tyname a -> Maybe (Type tyname a)) ->
  (name a -> Maybe (Term tyname name a)) ->
  Term tyname name a ->
  Term tyname name a
substTerm tynameF nameF = hoist f
  where
    f(VarF a bnd)         = case nameF bnd of
      Just t  -> project t
      Nothing -> VarF a bnd
    f(LamAbsF a bnd ty t) = LamAbsF a bnd (substTy tynameF ty) t
    f(TyInstF a t ty)     = TyInstF a t (substTy tynameF ty)
    f(WrapF a bnd ty t)   = WrapF a bnd (substTy tynameF ty) t
    f(ErrorF a ty)        = ErrorF a (substTy tynameF ty)
    f(x)                  = x

-- | Naively substitute names using the given function (i.e. do not account for scoping).
substTy ::
  (tyname a -> Maybe (Type tyname a)) ->
  Type tyname a ->
  Type tyname a
substTy tynameF = hoist f
  where
    f(TyVarF a ty)          = case tynameF ty of
      Just t  -> project t
      Nothing -> TyVarF a ty
    f(x)                    = x

-- | Safely substitute names using the given functions.
captureAvoidingSubstTerm ::
  (TyName a -> Maybe (Type TyName a)) ->
  (Name a -> Maybe (Term TyName Name a)) ->
  Term TyName Name a ->
  Term TyName Name a
captureAvoidingSubstTerm tynameF nameF t = let
    maxUnique = maxUniqueTerm t
    upscaleTerm = pure . (incTermUniques (maxUnique+1))
    upscaleType = pure . (incTypeUniques (maxUnique+1))
  in
    substTerm (upscaleType <=< tynameF) (upscaleTerm <=< nameF) t

-- | Safely substitute names using the given function.
captureAvoidingSubstTy ::
  (TyName a -> Maybe (Type TyName a)) ->
  Type TyName a ->
  Type TyName a
captureAvoidingSubstTy tynameF t = let
    maxUnique = maxUniqueTy t
    upscaleType = pure . (incTypeUniques (maxUnique+1))
  in
    substTy (upscaleType <=< tynameF) t

-- Free variables

-- | Get all the free term variables in a term.
fvTerm :: (Ord (name a)) => Term tyname name a -> Set (name a)
fvTerm = cata f
  where
    f(VarF _ n)        = singleton n
    f(TyAbsF _ _ _ t)  = t
    f(LamAbsF _ n _ t) = delete n t
    f(ApplyF _ t1 t2)  = union t1 t2
    f(TyInstF _ t _)   = t
    f(UnwrapF _ t)     = t
    f(WrapF _ _ _ t)   = t
    f(_)               = empty

-- | Get all the free type variables in a term.
ftvTerm :: (Ord (tyname a)) => Term tyname name a -> Set (tyname a)
ftvTerm = cata f
  where
    f(TyAbsF _ ty _ t)  = delete ty t
    f(LamAbsF _ _ ty t) = union (ftvTy ty) t
    f(ApplyF _ t1 t2)   = union t1 t2
    f(TyInstF _ t ty)   = union t (ftvTy ty)
    f(UnwrapF _ t)      = t
    f(WrapF _ bnd ty t) = delete bnd (union (ftvTy ty) t)
    f(_)                = empty

-- | Get all the free type variables in a type.
ftvTy :: (Ord (tyname a)) => Type tyname a -> Set (tyname a)
ftvTy = cata f
  where
    f(TyVarF _ ty)          = singleton ty
    f(TyFunF _ i o)         = union i o
    f(TyFixF _ bnd ty)      = delete bnd ty
    f(TyForallF _ bnd _ ty) = delete bnd ty
    f(TyLamF _ bnd _ ty)    = delete bnd ty
    f(TyAppF _ ty1 ty2)     = union ty1 ty2
    f(_)                    = empty
