-- editorconfig-checker-disable-file
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
module PlutusIR.Subst
    ( fvTerm
    , ftvTerm
    , fvBinding
    , ftvBinding
    , ftvTy
    , vTerm
    , tvTerm
    , tvTy
    ) where

import PlutusCore.Core (typeTyVars)
import PlutusCore.Core qualified as PLC
import PlutusCore.Subst (ftvTy, ftvTyCtx, tvTy)

import PlutusIR.Core

import Control.Lens
import Control.Lens.Unsound qualified as Unsound
import Data.Set as S hiding (foldr)
import Data.Set.Lens (setOf)
import Data.Traversable (mapAccumL)

-- | Get all the free term variables in a PIR term.
fvTerm :: Ord name => Traversal' (Term tyname name uni fun ann) name
fvTerm = fvTermCtx mempty

fvTermCtx :: Ord name => S.Set name -> Traversal' (Term tyname name uni fun ann) name
fvTermCtx bound f = \case
    Let a r@NonRec bs tIn ->
        let fvLinearScope boundSoFar b = (boundSoFar `union` setOf bindingNames b, fvBindingCtx boundSoFar f b)
            (boundAtTheEnd, bs') = mapAccumL fvLinearScope bound bs
        in Let a r <$> sequenceA bs' <*> fvTermCtx boundAtTheEnd f tIn
    Let a r@Rec bs tIn ->
        let bound' = bound `union` setOf (traversed . bindingNames) bs
        in Let a r <$> traverse (fvBindingCtx bound f) bs <*> fvTermCtx bound' f tIn

    Var a n         -> Var a <$> (if S.member n bound then pure n else f n)
    LamAbs a n ty t -> LamAbs a n ty <$> fvTermCtx (S.insert n bound) f t
    t -> (termSubterms . fvTermCtx bound) f t

-- | Get all the free type variables in a PIR term.
ftvTerm :: Ord tyname => Traversal' (Term tyname name uni fun ann) tyname
ftvTerm = ftvTermCtx mempty

ftvTermCtx :: Ord tyname => Set tyname -> Traversal' (Term tyname name uni fun ann) tyname
ftvTermCtx bound f = \case
    Let a r@NonRec bs tIn ->
        let ftvLinearScope bound' b = (bound' `union` setOf bindingTyNames b, ftvBindingCtx r bound' f b)
            (bound'', bs') = mapAccumL ftvLinearScope bound bs
        in Let a r <$> sequenceA bs' <*> ftvTermCtx bound'' f tIn

    Let a r@Rec bs tIn ->
        let bound' = bound `union` setOf (traversed . bindingTyNames) bs
        in Let a r <$> traverse (ftvBindingCtx r bound f) bs <*> ftvTermCtx bound' f tIn

    TyAbs a tn k t    -> TyAbs a tn k <$> ftvTermCtx (S.insert tn bound) f t
    -- sound because the subterms and subtypes are disjoint
    t -> ((termSubterms . ftvTermCtx bound) `Unsound.adjoin` (termSubtypes . ftvTyCtx bound)) f t

-- | Get all the free variables in a PIR single let-binding.
fvBinding :: Ord name => Traversal' (Binding tyname name uni fun ann) name
fvBinding = fvBindingCtx mempty

fvBindingCtx :: Ord name => Set name -> Traversal' (Binding tyname name uni fun ann) name
fvBindingCtx bound = bindingSubterms . fvTermCtx bound

-- | Get all the free type variables in a PIR single let-binding.
ftvBinding :: Ord tyname => Recursivity -> Traversal' (Binding tyname name uni fun ann) tyname
ftvBinding r = ftvBindingCtx r mempty

ftvBindingCtx :: Ord tyname => Recursivity -> Set tyname -> Traversal' (Binding tyname name uni fun ann) tyname
ftvBindingCtx r bound f = \case
    DatatypeBind a d -> DatatypeBind a <$> ftvDatatypeCtx r bound f d
    -- sound because the subterms and subtypes are disjoint
    b                -> ((bindingSubterms . ftvTermCtx bound) `Unsound.adjoin` (bindingSubtypes . ftvTyCtx bound)) f b

ftvDatatypeCtx :: Ord tyname => Recursivity -> Set tyname -> Traversal' (Datatype tyname name uni ann) tyname
ftvDatatypeCtx r bound f d@(Datatype a tyconstr tyvars destr constrs) =
    let
        tyConstr = setOf PLC.tyVarDeclName tyconstr
        tyVars = setOf (traversed.PLC.tyVarDeclName) tyvars
        allBound = bound `union` tyConstr `union` tyVars
        varsBound = bound `union` tyVars
    in case r of
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
            in Datatype a tyconstr tyvars destr <$> constrs'

-- | Traverse the arguments of a function type (nothing if the type is not a function type).
funArgs :: Traversal' (Type tyname uni a) (Type tyname uni a)
funArgs f = \case
    TyFun a dom cod@TyFun{} -> TyFun a <$> f dom <*> funArgs f cod
    TyFun a dom res         -> TyFun a <$> f dom <*> pure res
    t                       -> pure t

-- | Traverse the result type of a function type (the type itself if it is not a function type).
funRes :: Lens' (Type tyname uni a) (Type tyname uni a)
funRes f = \case
    TyFun a dom cod -> TyFun a dom <$> funRes f cod
    t               -> f t

-- TODO: these could be Traversals
-- | Get all the term variables in a term.
vTerm :: Fold (Term tyname name uni fun ann) name
vTerm = termSubtermsDeep . termVars

-- | Get all the type variables in a term.
tvTerm :: Fold (Term tyname name uni fun ann) tyname
tvTerm = termSubtypesDeep . typeTyVars
