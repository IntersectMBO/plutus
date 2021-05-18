{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
module PlutusIR.Core.Plated
    ( termSubterms
    , termSubtermsDeep
    , termSubtypes
    , termSubtypesDeep
    , termBindings
    , typeSubtypes
    , typeSubtypesDeep
    , typeUniques
    , typeUniquesDeep
    , datatypeSubtypes
    , bindingSubterms
    , bindingSubtypes
    , bindingIds
    , termUniques
    , termUniquesDeep
    ) where

import qualified PlutusCore             as PLC
import           PlutusCore.Core.Plated (typeSubtypes, typeSubtypesDeep, typeUniques, typeUniquesDeep)
import           PlutusCore.Flat        ()
import qualified PlutusCore.Name        as PLC

import           PlutusIR.Core.Type

import           Control.Lens           hiding (Strict)

infixr 6 <^>

-- | Compose two folds to make them run in parallel. The results are concatenated.
(<^>) :: Fold s a -> Fold s a -> Fold s a
(f1 <^> f2) g s = f1 g s *> f2 g s

{-# INLINE bindingSubterms #-}
-- | Get all the direct child 'Term's of the given 'Binding'.
bindingSubterms :: Traversal' (Binding tyname name uni fun a) (Term tyname name uni fun a)
bindingSubterms f = \case
    TermBind x s d t  -> TermBind x s d <$> f t
    b@TypeBind {}     -> pure b
    d@DatatypeBind {} -> pure d

{-# INLINE varDeclSubtypes #-}
-- | Get all the direct child 'Type's of the given 'VarDecl'.
varDeclSubtypes :: Traversal' (VarDecl tyname name uni fun a) (Type tyname uni a)
varDeclSubtypes f (VarDecl a n ty) = VarDecl a n <$> f ty

{-# INLINE datatypeSubtypes #-}
-- | Get all the direct child 'Type's of the given 'Datatype'.
datatypeSubtypes :: Traversal' (Datatype tyname name uni fun a) (Type tyname uni a)
datatypeSubtypes f (Datatype a n vs m cs) = Datatype a n vs m <$> (traverse . varDeclSubtypes) f cs

{-# INLINE bindingSubtypes #-}
-- | Get all the direct child 'Type's of the given 'Binding'.
bindingSubtypes :: Traversal' (Binding tyname name uni fun a) (Type tyname uni a)
bindingSubtypes f = \case
    TermBind x s d t -> TermBind x s <$> varDeclSubtypes f d <*> pure t
    DatatypeBind x d -> DatatypeBind x <$> datatypeSubtypes f d
    TypeBind a d ty  -> TypeBind a d <$> f ty

-- | All the identifiers/names introduced by this binding
-- In case of a datatype-binding it has multiple identifiers: the type, constructors, match function
bindingIds :: (PLC.HasUnique tyname PLC.TypeUnique, PLC.HasUnique name PLC.TermUnique)
            => Traversal' (Binding tyname name uni fun a) PLC.Unique
bindingIds f = \case
   TermBind x s d t -> TermBind x s <$> varDeclIds f d <*> pure t
   TypeBind a d ty -> TypeBind a <$> tyVarDeclIds f d <*> pure ty
   DatatypeBind a1 (Datatype a2 tvdecl tvdecls n vdecls) ->
     DatatypeBind a1 <$>
       (Datatype a2 <$> tyVarDeclIds f tvdecl
                    <*> traverse (tyVarDeclIds f) tvdecls
                    <*> PLC.theUnique f n
                    <*> traverse (varDeclIds f) vdecls)

tyVarDeclIds :: PLC.HasUnique tyname PLC.TypeUnique => Traversal' (TyVarDecl tyname a) PLC.Unique
tyVarDeclIds f (TyVarDecl a n b ) = TyVarDecl a <$> PLC.theUnique f n <*> pure b

varDeclIds :: PLC.HasUnique name PLC.TermUnique => Traversal' (VarDecl tyname name uni fun a) PLC.Unique
varDeclIds f (VarDecl a n b ) = VarDecl a <$> PLC.theUnique f n <*> pure b


{-# INLINE termSubterms #-}
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
    e@Error {}        -> pure e
    v@Var {}          -> pure v
    c@Constant {}     -> pure c
    b@Builtin {}      -> pure b

-- | Get all the transitive child 'Term's of the given 'Term'.
termSubtermsDeep :: Fold (Term tyname name uni fun ann) (Term tyname name uni fun ann)
termSubtermsDeep = cosmosOf termSubterms

{-# INLINE termSubtypes #-}
-- | Get all the direct child 'Type's of the given 'Term', including those within 'Binding's.
termSubtypes :: Traversal' (Term tyname name uni fun a) (Type tyname uni a)
termSubtypes f = \case
    Let x r bs t      -> Let x r <$> (traverse . bindingSubtypes) f bs <*> pure t
    LamAbs x n ty t   -> LamAbs x n <$> f ty <*> pure t
    TyInst x t ty     -> TyInst x t <$> f ty
    IWrap x ty1 ty2 t -> IWrap x <$> f ty1 <*> f ty2 <*> pure t
    Error x ty        -> Error x <$> f ty
    t@TyAbs {}        -> pure t
    a@Apply {}        -> pure a
    u@Unwrap {}       -> pure u
    v@Var {}          -> pure v
    c@Constant {}     -> pure c
    b@Builtin {}      -> pure b

-- | Get all the transitive child 'Type's of the given 'Term'.
termSubtypesDeep :: Fold (Term tyname name uni fun ann) (Type tyname uni ann)
termSubtypesDeep = termSubtermsDeep . termSubtypes . typeSubtypesDeep

{-# INLINE termBindings #-}
-- | Get all the direct child 'Binding's of the given 'Term'.
termBindings :: Traversal' (Term tyname name uni fun a) (Binding tyname name uni fun a)
termBindings f = \case
    Let x r bs t -> Let x r <$> traverse f bs <*> pure t
    t            -> pure t


-- | Get all the direct child 'Unique's of the given 'Term' (including the type-level ones).
termUniques
    :: PLC.HasUniques (Term tyname name uni fun ann)
    => Traversal' (Term tyname name uni fun ann) PLC.Unique
termUniques f = \case
    Let ann r bs t    -> Let ann r <$> (traverse . bindingIds) f bs <*> pure t
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

-- | Get all the transitive child 'Unique's of the given 'Term' (including the type-level ones).
termUniquesDeep
    :: PLC.HasUniques (Term tyname name uni fun ann)
    => Fold (Term tyname name uni fun ann) PLC.Unique
termUniquesDeep = termSubtermsDeep . (termSubtypes . typeUniquesDeep <^> termUniques)
