{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
module PlutusCore.Subst
    ( substTyVarA
    , substVarA
    , substTyVar
    , substVar
    , termSubstNamesM
    , termSubstTyNamesM
    , typeSubstTyNamesM
    , termSubstNames
    , termSubstTyNames
    , typeSubstTyNames
    , typeSubstClosedType
    , termSubstClosedType
    , termSubstClosedTerm
    , fvTerm
    , ftvTerm
    , ftvTy
    , ftvTyCtx
    , vTerm
    , tvTerm
    , tvTy
    ) where

import PlutusPrelude

import PlutusCore.Core

import Control.Lens
import Control.Lens.Unsound qualified as Unsound
import Data.Set as Set

purely :: ((a -> Identity b) -> c -> Identity d) -> (a -> b) -> c -> d
purely = coerce

{-# INLINE substTyVarA #-}
-- | Applicatively replace a type variable using the given function.
substTyVarA
    :: Applicative f
    => (tyname -> f (Maybe (Type tyname uni ann)))
    -> Type tyname uni ann
    -> f (Type tyname uni ann)
substTyVarA tynameF ty@(TyVar _ tyname) = fromMaybe ty <$> tynameF tyname
substTyVarA _       ty                  = pure ty

-- | Applicatively replace a variable using the given function.
substVarA
    :: Applicative f
    => (name -> f (Maybe (Term tyname name uni fun ann)))
    -> Term tyname name uni fun ann
    -> f (Term tyname name uni fun ann)
substVarA nameF t@(Var _ name) = fromMaybe t <$> nameF name
substVarA _     t              = pure t

-- | Replace a type variable using the given function.
substTyVar
    :: (tyname -> Maybe (Type tyname uni ann))
    -> Type tyname uni ann
    -> Type tyname uni ann
substTyVar = purely substTyVarA

-- | Replace a variable using the given function.
substVar
    :: (name -> Maybe (Term tyname name uni fun ann))
    -> Term tyname name uni fun ann
    -> Term tyname name uni fun ann
substVar = purely substVarA

{-# INLINE typeSubstTyNamesM #-}
-- | Naively monadically substitute type names (i.e. do not substitute binders).
-- INLINE is important here because the function is too polymorphic (determined from profiling)
typeSubstTyNamesM
    :: Monad m
    => (tyname -> m (Maybe (Type tyname uni ann)))
    -> Type tyname uni ann
    -> m (Type tyname uni ann)
typeSubstTyNamesM = transformMOf typeSubtypes . substTyVarA

-- | Naively monadically substitute names using the given function (i.e. do not substitute binders).
termSubstNamesM
    :: Monad m
    => (name -> m (Maybe (Term tyname name uni fun ann)))
    -> Term tyname name uni fun ann
    -> m (Term tyname name uni fun ann)
termSubstNamesM = transformMOf termSubterms . substVarA

-- | Naively monadically substitute type names using the given function
-- (i.e. do not substitute binders).
termSubstTyNamesM
    :: Monad m
    => (tyname -> m (Maybe (Type tyname uni ann)))
    -> Term tyname name uni fun ann
    -> m (Term tyname name uni fun ann)
termSubstTyNamesM =
    transformMOf termSubterms . traverseOf termSubtypes . transformMOf typeSubtypes . substTyVarA

-- | Naively substitute type names (i.e. do not substitute binders).
typeSubstTyNames
    :: (tyname -> Maybe (Type tyname uni ann))
    -> Type tyname uni ann
    -> Type tyname uni ann
typeSubstTyNames = purely typeSubstTyNamesM

-- | Naively substitute names using the given function (i.e. do not substitute binders).
termSubstNames
    :: (name -> Maybe (Term tyname name uni fun ann))
    -> Term tyname name uni fun ann
    -> Term tyname name uni fun ann
termSubstNames = purely termSubstNamesM

-- | Naively substitute type names using the given function (i.e. do not substitute binders).
termSubstTyNames
    :: (tyname -> Maybe (Type tyname uni ann))
    -> Term tyname name uni fun ann
    -> Term tyname name uni fun ann
termSubstTyNames = purely termSubstTyNamesM

-- | Substitute the given closed 'Type' for the given type variable in the given 'Type'. Does not
-- descend under binders that bind the same variable as the one we're substituting for (since from
-- there that variable is no longer free). The resulting 'Term' may and likely will not satisfy
-- global uniqueness.
typeSubstClosedType
    :: Eq tyname => tyname -> Type tyname uni a -> Type tyname uni a -> Type tyname uni a
typeSubstClosedType tn0 ty0 = go where
    go = \case
         TyVar    a tn      -> if tn == tn0 then ty0 else TyVar a tn
         TyForall a tn k ty -> TyForall a tn k (goUnder tn ty)
         TyLam    a tn k ty -> TyLam    a tn k (goUnder tn ty)
         ty                 -> ty & over typeSubtypes go
    goUnder tn ty = if tn == tn0 then ty else go ty

-- | Substitute the given closed 'Type' for the given type variable in the given 'Term'. Does not
-- descend under binders that bind the same variable as the one we're substituting for (since from
-- there that variable is no longer free). The resulting 'Term' may and likely will not satisfy
-- global uniqueness.
termSubstClosedType
    :: Eq tyname
    => tyname -> Type tyname uni a -> Term tyname name uni fun a -> Term tyname name uni fun a
termSubstClosedType tn0 ty0 = go where
    go = \case
         TyAbs a tn k body -> TyAbs a tn k (goUnder tn body)
         t                 -> t & over termSubtypes goTy & over termSubterms go
    goUnder tn term = if tn == tn0 then term else go term
    goTy = typeSubstClosedType tn0 ty0

-- | Substitute the given closed 'Term' for the given term variable in the given 'Term'. Does not
-- descend under binders that bind the same variable as the one we're substituting for (since from
-- there that variable is no longer free). The resulting 'Term' may and likely will not satisfy
-- global uniqueness.
termSubstClosedTerm
    :: Eq name
    => name
    -> Term tyname name uni fun a
    -> Term tyname name uni fun a
    -> Term tyname name uni fun a
termSubstClosedTerm varFor new = go where
    go = \case
         Var    a var         -> if var == varFor then new else Var a var
         LamAbs a var ty body -> LamAbs a var ty (goUnder var body)
         t                    -> t & over termSubterms go
    goUnder var term = if var == varFor then term else go term

-- Free variables

-- | Get all the free term variables in a term.
fvTerm :: Ord name => Traversal' (Term tyname name uni fun ann) name
fvTerm = fvTermCtx mempty

fvTermCtx :: Ord name => Set.Set name -> Traversal' (Term tyname name uni fun ann) name
fvTermCtx bound f = \case
    Var a n         -> Var a <$> (if Set.member n bound then pure n else f n)
    LamAbs a n ty t -> LamAbs a n ty <$> fvTermCtx (Set.insert n bound) f t
    t               -> (termSubterms . fvTermCtx bound) f t

-- | Get all the free type variables in a term.
ftvTerm :: Ord tyname => Traversal' (Term tyname name uni fun ann) tyname
ftvTerm = ftvTermCtx mempty

ftvTermCtx :: Ord tyname => Set.Set tyname -> Traversal' (Term tyname name uni fun ann) tyname
ftvTermCtx bound f = \case
    TyAbs a ty k t -> TyAbs a ty k <$> ftvTermCtx (Set.insert ty bound) f t
    -- sound because the subterms and subtypes are disjoint
    t              ->
        ((termSubterms . ftvTermCtx bound) `Unsound.adjoin` (termSubtypes . ftvTyCtx bound)) f t

-- | Get all the free type variables in a type.
ftvTy :: Ord tyname => Traversal' (Type tyname uni ann) tyname
ftvTy = ftvTyCtx mempty

ftvTyCtx :: Ord tyname => Set.Set tyname -> Traversal' (Type tyname uni ann) tyname
ftvTyCtx bound f = \case
    TyVar a ty          -> TyVar a <$> (if Set.member ty bound then pure ty else f ty)
    TyForall a bnd k ty -> TyForall a bnd k <$> ftvTyCtx (Set.insert bnd bound) f ty
    TyLam a bnd k ty    -> TyLam a bnd k <$> ftvTyCtx (Set.insert bnd bound) f ty
    t                   -> (typeSubtypes . ftvTyCtx bound) f t


-- TODO: these could be Traversals
-- | Get all the term variables in a term.
vTerm :: Fold (Term tyname name uni fun ann) name
vTerm = termSubtermsDeep . termVars

-- | Get all the type variables in a term.
tvTerm :: Fold (Term tyname name uni fun ann) tyname
tvTerm = termSubtypesDeep . typeTyVars

-- | Get all the type variables in a type.
tvTy :: Fold (Type tyname uni ann) tyname
tvTy = typeSubtypesDeep . typeTyVars
