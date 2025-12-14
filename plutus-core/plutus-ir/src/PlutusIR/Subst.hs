{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}

module PlutusIR.Subst
  ( substVarA
  , substTyVarA
  , typeSubstTyNames
  , termSubstNames
  , termSubstNamesM
  , termSubstTyNames
  , termSubstTyNamesM
  , bindingSubstNames
  , bindingSubstTyNames
  , fvTerm
  , ftvTerm
  , fvBinding
  , ftvBinding
  , ftvTy
  , vTerm
  , tvTerm
  , tvTy
  , substConstantA
  , substConstant
  , termSubstConstantsM
  , termSubstConstants
  ) where

import PlutusPrelude

import PlutusCore.Core (typeTyVars)
import PlutusCore.Core qualified as PLC
import PlutusCore.Name.Unique (HasUnique, TermUnique, TypeUnique)
import PlutusCore.Name.Unique qualified as PLC
import PlutusCore.Name.UniqueSet (UniqueSet)
import PlutusCore.Name.UniqueSet qualified as USet
import PlutusCore.Subst (ftvTy, ftvTyCtx, tvTy, typeSubstTyNames)
import PlutusIR.Core

import Control.Lens
import Control.Lens.Unsound qualified as Unsound
import Data.Traversable (mapAccumL)
import Universe

-- | Applicatively replace a variable using the given function.
substVarA
  :: Applicative f
  => (name -> f (Maybe (Term tyname name uni fun ann)))
  -> Term tyname name uni fun ann
  -> f (Term tyname name uni fun ann)
substVarA nameF t@(Var _ name) = fromMaybe t <$> nameF name
substVarA _ t = pure t
{-# INLINE substVarA #-}

-- | Applicatively replace a type variable using the given function.
substTyVarA
  :: Applicative f
  => (tyname -> f (Maybe (Type tyname uni ann)))
  -> Type tyname uni ann
  -> f (Type tyname uni ann)
substTyVarA tynameF ty@(TyVar _ tyname) = fromMaybe ty <$> tynameF tyname
substTyVarA _ ty = pure ty
{-# INLINE substTyVarA #-}

-- | Naively substitute names using the given functions (i.e. do not substitute binders).
termSubstNames
  :: (name -> Maybe (Term tyname name uni fun a))
  -> Term tyname name uni fun a
  -> Term tyname name uni fun a
termSubstNames = purely termSubstNamesM

-- | Naively monadically substitute names using the given function (i.e. do not substitute binders).
termSubstNamesM
  :: Monad m
  => (name -> m (Maybe (Term tyname name uni fun ann)))
  -> Term tyname name uni fun ann
  -> m (Term tyname name uni fun ann)
termSubstNamesM = transformMOf termSubterms . substVarA

-- | Naively substitute type names using the given functions (i.e. do not substitute binders).
termSubstTyNames
  :: (tyname -> Maybe (Type tyname uni a))
  -> Term tyname name uni fun a
  -> Term tyname name uni fun a
termSubstTyNames = purely termSubstTyNamesM

{-| Naively monadically substitute type names using the given function
(i.e. do not substitute binders). -}
termSubstTyNamesM
  :: Monad m
  => (tyname -> m (Maybe (Type tyname uni ann)))
  -> Term tyname name uni fun ann
  -> m (Term tyname name uni fun ann)
termSubstTyNamesM =
  transformMOf termSubterms . traverseOf termSubtypes . transformMOf typeSubtypes . substTyVarA

-- | Naively substitute names using the given functions (i.e. do not substitute binders).
bindingSubstNames
  :: (name -> Maybe (Term tyname name uni fun a))
  -> Binding tyname name uni fun a
  -> Binding tyname name uni fun a
bindingSubstNames nameF = over bindingSubterms (termSubstNames nameF)

-- | Naively substitute type names using the given functions (i.e. do not substitute binders).
bindingSubstTyNames
  :: (tyname -> Maybe (Type tyname uni a))
  -> Binding tyname name uni fun a
  -> Binding tyname name uni fun a
bindingSubstTyNames tynameF =
  over bindingSubterms (termSubstTyNames tynameF)
    . over bindingSubtypes (typeSubstTyNames tynameF)

-- | Get all the free term variables in a PIR term.
fvTerm :: HasUnique name TermUnique => Traversal' (Term tyname name uni fun ann) name
fvTerm = fvTermCtx mempty

fvTermCtx
  :: forall tyname name uni fun ann
   . HasUnique name TermUnique
  => UniqueSet TermUnique
  -> Traversal' (Term tyname name uni fun ann) name
fvTermCtx bound f = \case
  Let a r@NonRec bs tIn ->
    let fvLinearScope boundSoFar b =
          (boundSoFar `USet.union` USet.setOfByName bindingNames b, fvBindingCtx boundSoFar f b)
        (boundAtTheEnd, bs') = mapAccumL fvLinearScope bound bs
     in Let a r <$> sequenceA bs' <*> fvTermCtx boundAtTheEnd f tIn
  Let a r@Rec bs tIn ->
    let bound' = bound `USet.union` USet.setOfByName (traversed . bindingNames) bs
     in Let a r <$> traverse (fvBindingCtx bound f) bs <*> fvTermCtx bound' f tIn
  Var a n -> Var a <$> (if USet.memberByName n bound then pure n else f n)
  LamAbs a n ty t -> LamAbs a n ty <$> fvTermCtx (USet.insertByName n bound) f t
  t -> (termSubterms . fvTermCtx bound) f t

-- | Get all the free type variables in a PIR term.
ftvTerm :: HasUnique tyname TypeUnique => Traversal' (Term tyname name uni fun ann) tyname
ftvTerm = ftvTermCtx mempty

ftvTermCtx
  :: HasUnique tyname TypeUnique
  => UniqueSet TypeUnique
  -> Traversal' (Term tyname name uni fun ann) tyname
ftvTermCtx bound f = \case
  Let a r@NonRec bs tIn ->
    let ftvLinearScope bound' b =
          (bound' `USet.union` USet.setOfByName bindingTyNames b, ftvBindingCtx r bound' f b)
        (bound'', bs') = mapAccumL ftvLinearScope bound bs
     in Let a r <$> sequenceA bs' <*> ftvTermCtx bound'' f tIn
  Let a r@Rec bs tIn ->
    let bound' = bound `USet.union` USet.setOfByName (traversed . bindingTyNames) bs
     in Let a r <$> traverse (ftvBindingCtx r bound f) bs <*> ftvTermCtx bound' f tIn
  TyAbs a tn k t -> TyAbs a tn k <$> ftvTermCtx (USet.insertByName tn bound) f t
  -- sound because the subterms and subtypes are disjoint
  t -> ((termSubterms . ftvTermCtx bound) `Unsound.adjoin` (termSubtypes . ftvTyCtx bound)) f t

-- | Get all the free variables in a PIR single let-binding.
fvBinding :: HasUnique name TermUnique => Traversal' (Binding tyname name uni fun ann) name
fvBinding = fvBindingCtx mempty

fvBindingCtx
  :: HasUnique name TermUnique
  => UniqueSet TermUnique
  -> Traversal' (Binding tyname name uni fun ann) name
fvBindingCtx bound = bindingSubterms . fvTermCtx bound

-- | Get all the free type variables in a PIR single let-binding.
ftvBinding
  :: HasUnique tyname TypeUnique
  => Recursivity
  -> Traversal' (Binding tyname name uni fun ann) tyname
ftvBinding r = ftvBindingCtx r mempty

ftvBindingCtx
  :: HasUnique tyname TypeUnique
  => Recursivity
  -> UniqueSet TypeUnique
  -> Traversal' (Binding tyname name uni fun ann) tyname
ftvBindingCtx r bound f = \case
  DatatypeBind a d -> DatatypeBind a <$> ftvDatatypeCtx r bound f d
  -- sound because the subterms and subtypes are disjoint
  b ->
    ( (bindingSubterms . ftvTermCtx bound)
        `Unsound.adjoin` (bindingSubtypes . ftvTyCtx bound)
    )
      f
      b

ftvDatatypeCtx
  :: HasUnique tyname TypeUnique
  => Recursivity
  -> UniqueSet TypeUnique
  -> Traversal' (Datatype tyname name uni ann) tyname
ftvDatatypeCtx r bound f d@(Datatype a tyconstr tyvars destr constrs) =
  let
    tyConstr = USet.setOfByName PLC.tyVarDeclName tyconstr
    tyVars = USet.setOfByName (traversed . PLC.tyVarDeclName) tyvars
    allBound = bound `USet.union` tyConstr `USet.union` tyVars
    varsBound = bound `USet.union` tyVars
   in
    case r of
      -- recursive: introduced names are in scope throughout
      Rec -> (datatypeSubtypes . ftvTyCtx allBound) f d
      -- nonrecursive: type constructor is in scope only in the result type of the constructors
      NonRec ->
        let
          combinedTraversal =
            -- type arguments are in scope in the argument types
            (funArgs . ftvTyCtx varsBound)
              -- sound because the argument types and result type are disjoint
              `Unsound.adjoin`
              -- type constructor and arguments are in scope in the result type
              (funRes . ftvTyCtx allBound)
          constrs' = traverseOf (traversed . PLC.varDeclType . combinedTraversal) f constrs
         in
          Datatype a tyconstr tyvars destr <$> constrs'

-- | Traverse the arguments of a function type (nothing if the type is not a function type).
funArgs :: Traversal' (Type tyname uni a) (Type tyname uni a)
funArgs f = \case
  TyFun a dom cod@TyFun {} -> TyFun a <$> f dom <*> funArgs f cod
  TyFun a dom res -> TyFun a <$> f dom <*> pure res
  t -> pure t

-- | Traverse the result type of a function type (the type itself if it is not a function type).
funRes :: Lens' (Type tyname uni a) (Type tyname uni a)
funRes f = \case
  TyFun a dom cod -> TyFun a dom <$> funRes f cod
  t -> f t

-- TODO: these could be Traversals
-- | Get all the term variables in a term.
vTerm :: Fold (Term tyname name uni fun ann) name
vTerm = termSubtermsDeep . termVars

-- | Get all the type variables in a term.
tvTerm :: Fold (Term tyname name uni fun ann) tyname
tvTerm = termSubtypesDeep . typeTyVars

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
