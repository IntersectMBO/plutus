-- editorconfig-checker-disable-file
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
    , termSubstFreeNamesA
    , termSubstFreeNames
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
import PlutusCore.Name

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

-- | Naively monadically substitute type names using the given function (i.e. do not substitute binders).
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

-- | Applicatively substitute *free* names using the given function.
termSubstFreeNamesA
    :: (Applicative f, HasUnique name TermUnique)
    => (name -> f (Maybe (Term tyname name uni fun ann)))
    -> Term tyname name uni fun ann
    -> f (Term tyname name uni fun ann)
termSubstFreeNamesA f = go Set.empty where
    go bvs var@(Var _ name)           =
        if (name ^. unique) `member` bvs
            then pure var
            else fromMaybe var <$> f name
    go bvs (TyAbs ann name kind body) = TyAbs ann name kind <$> go bvs body
    go bvs (LamAbs ann name ty body)  = LamAbs ann name ty <$> go (insert (name ^. unique) bvs) body
    go bvs (Apply ann fun arg)        = Apply ann <$> go bvs fun <*> go bvs arg
    go bvs (TyInst ann term ty)       = go bvs term <&> \term' -> TyInst ann term' ty
    go bvs (Unwrap ann term)          = Unwrap ann <$> go bvs term
    go bvs (IWrap ann pat arg term)   = IWrap ann pat arg <$> go bvs term
    go _   term@Constant{}            = pure term
    go _   term@Builtin{}             = pure term
    go _   term@Error{}               = pure term

-- | Substitute *free* names using the given function.
termSubstFreeNames
    :: HasUnique name TermUnique
    => (name -> Maybe (Term tyname name uni fun ann))
    -> Term tyname name uni fun ann
    -> Term tyname name uni fun ann
termSubstFreeNames = purely termSubstFreeNamesA

-- | Substitute a closed 'Type' for a type variable in a 'Type'. Does not descend under binders that
-- bind the same variable as the one we're substituting for. The resulting 'Term' may and likely
-- will not satisfy global uniqueness.
typeSubstClosedType
    :: Eq tyname
    => tyname -> Type tyname uni () -> Type tyname uni () -> Type tyname uni ()
typeSubstClosedType tn0 ty0 = go where
    go = \case
         TyVar    () tn      -> if tn == tn0 then ty0 else TyVar () tn
         TyFun    () ty1 ty2 -> TyFun    () (go ty1) (go ty2)
         TyIFix   () ty1 ty2 -> TyIFix   () (go ty1) (go ty2)
         TyApp    () ty1 ty2 -> TyApp    () (go ty1) (go ty2)
         TyForall () tn k ty -> TyForall () tn k (goUnder tn ty)
         TyLam    () tn k ty -> TyLam    () tn k (goUnder tn ty)
         bt@TyBuiltin{}      -> bt
    goUnder tn ty = if tn == tn0 then ty else go ty

-- | Substitute a closed 'Type' for a type variable in a 'Term'. Does not descend under binders that
-- bind the same variable as the one we're substituting for. The resulting 'Term' may and likely
-- will not satisfy global uniqueness.
termSubstClosedType
    :: Eq tyname
    => tyname -> Type tyname uni () -> Term tyname name uni fun () -> Term tyname name uni fun ()
termSubstClosedType tn0 ty0 = go where
    go = \case
         v@Var{}                 -> v
         c@Constant{}            -> c
         b@Builtin{}             -> b
         TyAbs   () tn ty body   -> TyAbs   () tn ty (goUnder tn body)
         LamAbs  () var ty body  -> LamAbs  () var (goTy ty) (go body)
         Apply   () fun arg      -> Apply   () (go fun) (go arg)
         TyInst  () fun ty       -> TyInst  () (go fun) (goTy ty)
         Unwrap  () term         -> Unwrap  () (go term)
         IWrap   () pat arg term -> IWrap   () (goTy pat) (goTy arg) (go term)
         Error   () ty           -> Error   () (goTy ty)
    goUnder tn term = if tn == tn0 then term else go term
    goTy = typeSubstClosedType tn0 ty0

-- | Substitute a closed 'Term' for a term variable in a 'Term'. Does not descend under binders that
-- bind the same variable as the one we're substituting for. The resulting 'Term' may and likely
-- will not satisfy global uniqueness.
termSubstClosedTerm
    :: Eq name
    => name -> Term tyname name uni fun () -> Term tyname name uni fun () -> Term tyname name uni fun ()
termSubstClosedTerm varFor new = go where
    go = \case
         Var      () var          -> if var == varFor then new else Var () var
         TyAbs    () tyn ty body  -> TyAbs    () tyn ty (go body)
         LamAbs   () var ty body  -> LamAbs   () var ty (goUnder var body)
         Apply    () fun arg      -> Apply    () (go fun) (go arg)
         Constant () constant     -> Constant () constant
         TyInst   () fun arg      -> TyInst   () (go fun) arg
         Unwrap   () term         -> Unwrap   () (go term)
         IWrap    () pat arg term -> IWrap    () pat arg (go term)
         b@Builtin{}              -> b
         e@Error  {}              -> e
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
    t              -> ((termSubterms . ftvTermCtx bound) `Unsound.adjoin` (termSubtypes . ftvTyCtx bound)) f t

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
