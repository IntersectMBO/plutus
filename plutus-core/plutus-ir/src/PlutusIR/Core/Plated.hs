-- editorconfig-checker-disable-file
{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE LambdaCase    #-}
{-# LANGUAGE RankNTypes    #-}
module PlutusIR.Core.Plated
    ( termSubterms
    , termSubtermsDeep
    , termSubtypes
    , termSubtypesDeep
    , termSubkinds
    , termBindings
    , termVars
    , termConstants
    , termConstantsDeep
    , typeSubtypes
    , typeSubtypesDeep
    , typeSubkinds
    , typeUniques
    , typeUniquesDeep
    , datatypeSubtypes
    , datatypeSubkinds
    , datatypeTyNames
    , bindingSubterms
    , bindingSubtypes
    , bindingSubkinds
    , bindingNames
    , bindingTyNames
    , bindingIds
    , termUniques
    , termUniquesDeep
    , varDeclSubtypes
    , underBinders
    , _Constant
    ) where

import PlutusCore qualified as PLC
import PlutusCore.Arity
import PlutusCore.Core (tyVarDeclSubkinds, typeSubkinds, typeSubtypes, typeSubtypesDeep,
                        typeUniques, typeUniquesDeep, varDeclSubtypes)
import PlutusCore.FlatInstances ()
import PlutusCore.Name.Unique qualified as PLC

import PlutusIR.Core.Type

import Control.Lens hiding (Strict, (<.>))
import Data.Functor.Apply
import Data.Functor.Bind.Class
import Universe

infixr 6 <^>

-- | Compose two folds to make them run in parallel. The results are concatenated.
(<^>) :: Fold s a -> Fold s a -> Fold s a
(f1 <^> f2) g s = f1 g s *> f2 g s

-- | View a term as a constant.
_Constant :: Prism' (Term tyname name uni fun a) (a, PLC.Some (PLC.ValueOf uni))
_Constant = prism' (uncurry Constant) (\case { Constant a v -> Just (a, v); _ -> Nothing })

-- | Get all the direct child 'Term's of the given 'Binding'.
bindingSubterms :: Traversal' (Binding tyname name uni fun a) (Term tyname name uni fun a)
bindingSubterms f = \case
    TermBind x s d t  -> TermBind x s d <$> f t
    b@TypeBind {}     -> pure b
    d@DatatypeBind {} -> pure d
{-# INLINE bindingSubterms #-}

-- | Get all the direct child 'Type's of the given 'Datatype'.
datatypeSubtypes :: Traversal' (Datatype tyname name uni a) (Type tyname uni a)
datatypeSubtypes f (Datatype a n vs m cs) = Datatype a n vs m <$> (traverse . varDeclSubtypes) f cs
{-# INLINE datatypeSubtypes #-}

-- | Get all the direct child 'Type's of the given 'Binding'.
bindingSubtypes :: Traversal' (Binding tyname name uni fun a) (Type tyname uni a)
bindingSubtypes f = \case
    TermBind x s d t -> TermBind x s <$> varDeclSubtypes f d <*> pure t
    DatatypeBind x d -> DatatypeBind x <$> datatypeSubtypes f d
    TypeBind a d ty  -> TypeBind a d <$> f ty
{-# INLINE bindingSubtypes #-}

-- | Get all the direct child 'Kind's of the given 'Datatype'.
datatypeSubkinds :: Traversal' (Datatype tyname name uni a) (Kind a)
datatypeSubkinds f (Datatype a n vs m cs) = do
    n' <- tyVarDeclSubkinds f n
    vs' <- traverse (tyVarDeclSubkinds f) vs
    pure $ Datatype a n' vs' m cs
{-# INLINE datatypeSubkinds #-}

-- | Get all the type-names introduces by a datatype
datatypeTyNames :: Traversal' (Datatype tyname name uni a) tyname
datatypeTyNames f (Datatype a2 tvdecl tvdecls n vdecls) =
    Datatype a2
        <$> PLC.tyVarDeclName f tvdecl
        <*> traverse (PLC.tyVarDeclName f) tvdecls
        <*> pure n
        <*> pure vdecls
{-# INLINE datatypeTyNames #-}

-- | Get all the direct child 'Kind's of the given 'Binding'.
bindingSubkinds :: Traversal' (Binding tyname name uni fun a) (Kind a)
bindingSubkinds f = \case
    t@TermBind {}    -> pure t
    DatatypeBind x d -> DatatypeBind x <$> datatypeSubkinds f d
    TypeBind a d ty  -> TypeBind a <$> tyVarDeclSubkinds f d <*> pure ty
{-# INLINE bindingSubkinds #-}

-- | All the identifiers/names introduced by this binding
-- In case of a datatype-binding it has multiple identifiers: the type, constructors, match function
bindingIds :: (PLC.HasUnique tyname PLC.TypeUnique, PLC.HasUnique name PLC.TermUnique)
            => Traversal1' (Binding tyname name uni fun a) PLC.Unique
bindingIds f = \case
   TermBind x s d t -> flip (TermBind x s) t <$> (PLC.varDeclName . PLC.theUnique) f d
   TypeBind a d ty -> flip (TypeBind a) ty <$> (PLC.tyVarDeclName . PLC.theUnique) f d
   DatatypeBind a1 (Datatype a2 tvdecl tvdecls n vdecls) ->
     DatatypeBind a1 <$>
       (Datatype a2 <$> (PLC.tyVarDeclName . PLC.theUnique) f tvdecl
                    <.*> traverse1Maybe ((PLC.tyVarDeclName . PLC.theUnique) f) tvdecls
                    <.> PLC.theUnique f n
                    <.*> traverse1Maybe ((PLC.varDeclName . PLC.theUnique) f) vdecls)

-- | Get all the direct constants of the given 'Term' from 'Constant's.
termConstants :: Traversal' (Term tyname name uni fun ann) (Some (ValueOf uni))
termConstants f term0 = case term0 of
    Constant ann val -> Constant ann <$> f val
    Let{}            -> pure term0
    Var{}            -> pure term0
    TyAbs{}          -> pure term0
    LamAbs{}         -> pure term0
    TyInst{}         -> pure term0
    IWrap{}          -> pure term0
    Error{}          -> pure term0
    Apply{}          -> pure term0
    Unwrap{}         -> pure term0
    Builtin{}        -> pure term0
    Constr{}         -> pure term0
    Case{}           -> pure term0

-- | Get all the direct child 'Kind's of the given 'Term'.
termSubkinds :: Traversal' (Term tyname name uni fun ann) (Kind ann)
termSubkinds f term0 = case term0 of
    Let x r bs t    -> Let x r <$> (traverse . bindingSubkinds) f bs <*> pure t
    TyAbs ann n k t -> f k <&> \k' -> TyAbs ann n k' t
    LamAbs{}        -> pure term0
    Var{}           -> pure term0
    TyInst{}        -> pure term0
    IWrap{}         -> pure term0
    Error{}         -> pure term0
    Apply{}         -> pure term0
    Unwrap{}        -> pure term0
    Constant{}      -> pure term0
    Builtin{}       -> pure term0
    Constr{}        -> pure term0
    Case{}          -> pure term0
{-# INLINE termSubkinds #-}

-- | Get all the direct child 'Term's of the given 'Term', including those within 'Binding's.
termSubterms :: Traversal' (Term tyname name uni fun a) (Term tyname name uni fun a)
termSubterms f = \case
    Let x r bs t      -> Let x r <$> (traverse . bindingSubterms) f bs <*> f t
    TyAbs x tn k t    -> TyAbs x tn k <$> f t
    LamAbs x n ty t   -> LamAbs x n ty <$> f t
    Apply x t1 t2     -> Apply x <$> f t1 <*> f t2
    TyInst x t ty     -> TyInst x <$> f t <*> pure ty
    IWrap x ty1 ty2 t -> IWrap x ty1 ty2 <$> f t
    Unwrap x t        -> Unwrap x <$> f t
    Constr x ty i es  -> Constr x ty i <$> traverse f es
    Case x ty arg cs  -> Case x ty <$> f arg <*> traverse f cs
    e@Error {}        -> pure e
    v@Var {}          -> pure v
    c@Constant {}     -> pure c
    b@Builtin {}      -> pure b
{-# INLINE termSubterms #-}

-- | Get all the transitive child 'Term's of the given 'Term'.
termSubtermsDeep :: Fold (Term tyname name uni fun ann) (Term tyname name uni fun ann)
termSubtermsDeep = cosmosOf termSubterms

-- | Get all the direct child 'Type's of the given 'Term', including those within 'Binding's.
termSubtypes :: Traversal' (Term tyname name uni fun a) (Type tyname uni a)
termSubtypes f = \case
    Let x r bs t      -> Let x r <$> (traverse . bindingSubtypes) f bs <*> pure t
    LamAbs x n ty t   -> LamAbs x n <$> f ty <*> pure t
    TyInst x t ty     -> TyInst x t <$> f ty
    IWrap x ty1 ty2 t -> IWrap x <$> f ty1 <*> f ty2 <*> pure t
    Error x ty        -> Error x <$> f ty
    Constr x ty i es  -> Constr x <$> f ty <*> pure i <*> pure es
    Case x ty arg cs  -> Case x <$> f ty <*> pure arg <*> pure cs
    t@TyAbs {}        -> pure t
    a@Apply {}        -> pure a
    u@Unwrap {}       -> pure u
    v@Var {}          -> pure v
    c@Constant {}     -> pure c
    b@Builtin {}      -> pure b
{-# INLINE termSubtypes #-}

-- | Get all the transitive child 'Type's of the given 'Term'.
termSubtypesDeep :: Fold (Term tyname name uni fun ann) (Type tyname uni ann)
termSubtypesDeep = termSubtermsDeep . termSubtypes . typeSubtypesDeep

-- | Get all the direct child 'Binding's of the given 'Term'.
termBindings :: Traversal' (Term tyname name uni fun a) (Binding tyname name uni fun a)
termBindings f = \case
    Let x r bs t -> Let x r <$> traverse f bs <*> pure t
    t            -> pure t
{-# INLINE termBindings #-}

-- | Get all the direct child 'Unique's of the given 'Term' (including the type-level ones).
termUniques
    :: PLC.HasUniques (Term tyname name uni fun ann)
    => Traversal' (Term tyname name uni fun ann) PLC.Unique
termUniques f = \case
    Let ann r bs t    -> Let ann r <$> cloneTraversal (traversed.bindingIds) f bs <*> pure t
    Var ann n         -> PLC.theUnique f n  <&> Var ann
    TyAbs ann tn k t  -> PLC.theUnique f tn <&> \tn' -> TyAbs ann tn' k t
    LamAbs ann n ty t -> PLC.theUnique f n  <&> \n'  -> LamAbs ann n' ty t
    a@Apply{}         -> pure a
    c@Constant{}      -> pure c
    b@Builtin{}       -> pure b
    t@TyInst{}        -> pure t
    e@Error{}         -> pure e
    i@IWrap{}         -> pure i
    u@Unwrap{}        -> pure u
    p@Constr {}       -> pure p
    p@Case {}         -> pure p

-- | Get all the direct child 'name a's of the given 'Term' from 'Var's.
termVars :: Traversal' (Term tyname name uni fun ann) name
termVars f term0 = case term0 of
    Var ann n -> Var ann <$> f n
    t         -> pure t

-- | Get all the transitive child 'Constant's of the given 'Term'.
termConstantsDeep :: Fold (Term tyname name uni fun ann) (Some (ValueOf uni))
termConstantsDeep = termSubtermsDeep . termConstants

-- | Get all the transitive child 'Unique's of the given 'Term' (including the type-level ones).
termUniquesDeep
    :: PLC.HasUniques (Term tyname name uni fun ann)
    => Fold (Term tyname name uni fun ann) PLC.Unique
termUniquesDeep = termSubtermsDeep . (termSubtypes . typeUniquesDeep <^> termUniques)

-- | Get all the names introduces by a binding
bindingNames :: Traversal' (Binding tyname name uni fun a) name
bindingNames f = \case
   TermBind x s d t -> TermBind x s <$> PLC.varDeclName f d <*> pure t
   DatatypeBind a1 (Datatype a2 tvdecl tvdecls n vdecls) ->
     DatatypeBind a1 <$>
       (Datatype a2 tvdecl tvdecls
                    <$> f n
                    <*> traverse (PLC.varDeclName f) vdecls)
   b@TypeBind{} -> pure b

-- | Get all the type-names introduces by a binding
bindingTyNames :: Traversal' (Binding tyname name uni fun a) tyname
bindingTyNames f = \case
   TypeBind a d ty   -> TypeBind a <$> PLC.tyVarDeclName f d <*> pure ty
   DatatypeBind a1 d -> DatatypeBind a1 <$> datatypeTyNames f d
   b@TermBind{}      -> pure b

-- | Focus on the term under the binders corresponding to the given arity.
-- e.g. for arity @[TermParam, TermParam]@ and term @\x y -> t@ it focusses on @t@.
underBinders :: Arity -> Traversal' (Term tyname name uni fun a) (Term tyname name uni fun a)
underBinders [] f t                                = f t
underBinders (TermParam:arity) f (LamAbs a n ty t) = LamAbs a n ty <$> underBinders arity f t
underBinders (TypeParam:arity) f (TyAbs a ty k t)  = TyAbs a ty k <$> underBinders arity f t
underBinders _ _ t                                 = pure t
