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
  , typeMapNames
  , termMapNames
  , programMapNames
  , fvTerm
  , ftvTerm
  , ftvTy
  , ftvTyCtx
  , vTerm
  , tvTerm
  , tvTy
  , substConstantA
  , substConstant
  , termSubstConstantsM
  , termSubstConstants
  ) where

import PlutusPrelude

import PlutusCore.Core

import Control.Lens
import Control.Lens.Unsound qualified as Unsound
import PlutusCore.Name.Unique (HasUnique)
import PlutusCore.Name.UniqueSet (UniqueSet)
import PlutusCore.Name.UniqueSet qualified as USet

import Universe

-- | Applicatively replace a type variable using the given function.
substTyVarA
  :: Applicative f
  => (tyname -> f (Maybe (Type tyname uni ann)))
  -> Type tyname uni ann
  -> f (Type tyname uni ann)
substTyVarA tynameF ty@(TyVar _ tyname) = fromMaybe ty <$> tynameF tyname
substTyVarA _ ty = pure ty
{-# INLINE substTyVarA #-}

-- | Applicatively replace a variable using the given function.
substVarA
  :: Applicative f
  => (name -> f (Maybe (Term tyname name uni fun ann)))
  -> Term tyname name uni fun ann
  -> f (Term tyname name uni fun ann)
substVarA nameF t@(Var _ name) = fromMaybe t <$> nameF name
substVarA _ t = pure t

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

{-| Naively monadically substitute type names (i.e. do not substitute binders).
INLINE is important here because the function is too polymorphic (determined from profiling) -}
typeSubstTyNamesM
  :: Monad m
  => (tyname -> m (Maybe (Type tyname uni ann)))
  -> Type tyname uni ann
  -> m (Type tyname uni ann)
typeSubstTyNamesM = transformMOf typeSubtypes . substTyVarA
{-# INLINE typeSubstTyNamesM #-}

-- | Naively monadically substitute names using the given function (i.e. do not substitute binders).
termSubstNamesM
  :: Monad m
  => (name -> m (Maybe (Term tyname name uni fun ann)))
  -> Term tyname name uni fun ann
  -> m (Term tyname name uni fun ann)
termSubstNamesM = transformMOf termSubterms . substVarA

{-| Naively monadically substitute type names using the given function
(i.e. do not substitute binders). -}
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

{-| Substitute the given closed 'Type' for the given type variable in the given 'Type'. Does not
descend under binders that bind the same variable as the one we're substituting for (since from
there that variable is no longer free). The resulting 'Term' may and likely will not satisfy
global uniqueness. -}
typeSubstClosedType
  :: Eq tyname => tyname -> Type tyname uni a -> Type tyname uni a -> Type tyname uni a
typeSubstClosedType tn0 ty0 = go
  where
    go = \case
      TyVar a tn -> if tn == tn0 then ty0 else TyVar a tn
      TyForall a tn k ty -> TyForall a tn k (goUnder tn ty)
      TyLam a tn k ty -> TyLam a tn k (goUnder tn ty)
      ty -> ty & over typeSubtypes go
    goUnder tn ty = if tn == tn0 then ty else go ty

{-| Substitute the given closed 'Type' for the given type variable in the given 'Term'. Does not
descend under binders that bind the same variable as the one we're substituting for (since from
there that variable is no longer free). The resulting 'Term' may and likely will not satisfy
global uniqueness. -}
termSubstClosedType
  :: Eq tyname
  => tyname -> Type tyname uni a -> Term tyname name uni fun a -> Term tyname name uni fun a
termSubstClosedType tn0 ty0 = go
  where
    go = \case
      TyAbs a tn k body -> TyAbs a tn k (goUnder tn body)
      t -> t & over termSubtypes goTy & over termSubterms go
    goUnder tn term = if tn == tn0 then term else go term
    goTy = typeSubstClosedType tn0 ty0

{-| Substitute the given closed 'Term' for the given term variable in the given 'Term'. Does not
descend under binders that bind the same variable as the one we're substituting for (since from
there that variable is no longer free). The resulting 'Term' may and likely will not satisfy
global uniqueness. -}
termSubstClosedTerm
  :: Eq name
  => name
  -> Term tyname name uni fun a
  -> Term tyname name uni fun a
  -> Term tyname name uni fun a
termSubstClosedTerm varFor new = go
  where
    go = \case
      Var a var -> if var == varFor then new else Var a var
      LamAbs a var ty body -> LamAbs a var ty (goUnder var body)
      t -> t & over termSubterms go
    goUnder var term = if var == varFor then term else go term

-- Mapping name-modification functions over types and terms.

typeMapNames
  :: forall tyname tyname' uni ann
   . (tyname -> tyname')
  -> Type tyname uni ann
  -> Type tyname' uni ann
typeMapNames f = go
  where
    go :: Type tyname uni ann -> Type tyname' uni ann
    go = \case
      TyVar ann tn -> TyVar ann (f tn)
      TyFun ann ty1 ty2 -> TyFun ann (go ty1) (go ty2)
      TyIFix ann ty1 ty2 -> TyIFix ann (go ty1) (go ty2)
      TyForall ann tn k ty -> TyForall ann (f tn) k (go ty)
      TyBuiltin ann s -> TyBuiltin ann s
      TyLam ann tn k ty -> TyLam ann (f tn) k (go ty)
      TyApp ann ty1 ty2 -> TyApp ann (go ty1) (go ty2)
      TySOP ann tyls -> TySOP ann ((fmap . fmap) go tyls)

-- termMapNames requires two function arguments: one (called f) to modify type names
-- and another (called g) to modify variable names.
termMapNames
  :: forall tyname tyname' name name' uni fun ann
   . (tyname -> tyname')
  -> (name -> name')
  -> Term tyname name uni fun ann
  -> Term tyname' name' uni fun ann
termMapNames f g = go
  where
    go :: Term tyname name uni fun ann -> Term tyname' name' uni fun ann
    go = \case
      LamAbs ann name ty body -> LamAbs ann (g name) (typeMapNames f ty) (go body)
      TyAbs ann tyname k body -> TyAbs ann (f tyname) k (go body)
      Var ann name -> Var ann (g name)
      Apply ann t1 t2 -> Apply ann (go t1) (go t2)
      Constant ann c -> Constant ann c
      Builtin ann b -> Builtin ann b
      TyInst ann body ty -> TyInst ann (go body) (typeMapNames f ty)
      Unwrap ann body -> Unwrap ann (go body)
      IWrap ann ty1 ty2 body -> IWrap ann (typeMapNames f ty1) (typeMapNames f ty2) (go body)
      Constr ann ty i es -> Constr ann (typeMapNames f ty) i (fmap go es)
      Case ann ty arg cs -> Case ann (typeMapNames f ty) (go arg) (fmap go cs)
      Error ann ty -> Error ann (typeMapNames f ty)

programMapNames
  :: forall tyname tyname' name name' uni fun ann
   . (tyname -> tyname')
  -> (name -> name')
  -> Program tyname name uni fun ann
  -> Program tyname' name' uni fun ann
programMapNames f g (Program a v term) = Program a v (termMapNames f g term)

-- Free variables

-- | Get all the free term variables in a term.
fvTerm :: HasUnique name unique => Traversal' (Term tyname name uni fun ann) name
fvTerm = fvTermCtx mempty

fvTermCtx
  :: HasUnique name unique
  => UniqueSet unique -> Traversal' (Term tyname name uni fun ann) name
fvTermCtx bound f = \case
  Var a n -> Var a <$> (if USet.memberByName n bound then pure n else f n)
  LamAbs a n ty t -> LamAbs a n ty <$> fvTermCtx (USet.insertByName n bound) f t
  t -> (termSubterms . fvTermCtx bound) f t

-- | Get all the free type variables in a term.
ftvTerm :: HasUnique tyname unique => Traversal' (Term tyname name uni fun ann) tyname
ftvTerm = ftvTermCtx mempty

ftvTermCtx
  :: HasUnique tyname unique
  => UniqueSet unique
  -> Traversal' (Term tyname name uni fun ann) tyname
ftvTermCtx bound f = \case
  TyAbs a ty k t -> TyAbs a ty k <$> ftvTermCtx (USet.insertByName ty bound) f t
  -- sound because the subterms and subtypes are disjoint
  t ->
    ((termSubterms . ftvTermCtx bound) `Unsound.adjoin` (termSubtypes . ftvTyCtx bound)) f t

-- | Get all the free type variables in a type.
ftvTy
  :: HasUnique tyname unique
  => Traversal' (Type tyname uni ann) tyname
ftvTy = ftvTyCtx mempty

ftvTyCtx
  :: HasUnique tyname unique
  => UniqueSet unique
  -> Traversal' (Type tyname uni ann) tyname
ftvTyCtx bound f = \case
  TyVar a ty -> TyVar a <$> (if USet.memberByName ty bound then pure ty else f ty)
  TyForall a bnd k ty -> TyForall a bnd k <$> ftvTyCtx (USet.insertByName bnd bound) f ty
  TyLam a bnd k ty -> TyLam a bnd k <$> ftvTyCtx (USet.insertByName bnd bound) f ty
  t -> (typeSubtypes . ftvTyCtx bound) f t

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

-- | Applicatively replace a constant using the given function.
substConstantA
  :: Applicative f
  => (ann -> Some (ValueOf uni) -> f (Maybe (Term tyname name uni fun ann)))
  -> Term tyname name uni fun ann
  -> f (Term tyname name uni fun ann)
substConstantA valF t@(Constant ann val) = fromMaybe t <$> valF ann val
substConstantA _ t = pure t

-- | Replace a constant using the given function.
substConstant
  :: (ann -> Some (ValueOf uni) -> Maybe (Term tyname name uni fun ann))
  -> Term tyname name uni fun ann
  -> Term tyname name uni fun ann
substConstant = purely (substConstantA . curry) . uncurry

-- | Monadically substitute constants using the given function.
termSubstConstantsM
  :: Monad m
  => (ann -> Some (ValueOf uni) -> m (Maybe (Term tyname name uni fun ann)))
  -> Term tyname name uni fun ann
  -> m (Term tyname name uni fun ann)
termSubstConstantsM = transformMOf termSubterms . substConstantA

-- | Substitute constants using the given function.
termSubstConstants
  :: (ann -> Some (ValueOf uni) -> Maybe (Term tyname name uni fun ann))
  -> Term tyname name uni fun ann
  -> Term tyname name uni fun ann
termSubstConstants = purely (termSubstConstantsM . curry) . uncurry
