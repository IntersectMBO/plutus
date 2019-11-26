{-# LANGUAGE LambdaCase #-}

module Language.PlutusCore.Type.Plated
    ( typeTyBinds
    , typeTyVars
    , typeSubtypes
    , typeSubtypesDeep
    , termTyBinds
    , termBinds
    , termVars
    , termSubtypes
    , termSubtypesDeep
    , termSubterms
    , termSubtermsDeep
    ) where

import           Language.PlutusCore.Type.Core

import           Control.Lens

-- | Get all the direct child 'tyname a's of the given 'Type' from binders.
typeTyBinds :: Traversal' (Type tyname ann) (tyname ann)
typeTyBinds f = \case
    TyForall ann tn k ty -> f tn <&> \tn' -> TyForall ann tn' k ty
    TyLam ann tn k ty -> f tn <&> \tn' -> TyLam ann tn' k ty
    x -> pure x

-- | Get all the direct child 'tyname a's of the given 'Type' from 'TyVar's.
typeTyVars :: Traversal' (Type tyname ann) (tyname ann)
typeTyVars f = \case
    TyVar ann n -> TyVar ann <$> f n
    x -> pure x

{-# INLINE typeSubtypes #-}
-- | Get all the direct child 'Type's of the given 'Type'.
typeSubtypes :: Traversal' (Type tyname ann) (Type tyname ann)
typeSubtypes f = \case
    TyFun ann ty1 ty2 -> TyFun ann <$> f ty1 <*> f ty2
    TyIFix ann pat arg -> TyIFix ann <$> f pat <*> f arg
    TyForall ann tn k ty -> TyForall ann tn k <$> f ty
    TyLam ann tn k ty -> TyLam ann tn k <$> f ty
    TyApp ann ty1 ty2 -> TyApp ann <$> f ty1 <*> f ty2
    b@TyBuiltin {} -> pure b
    v@TyVar {} -> pure v

-- | Get all the transitive child 'Type's of the given 'Type'.
typeSubtypesDeep
    :: (Applicative f, Contravariant f)
    => LensLike' f (Type tyname ann) (Type tyname ann)
typeSubtypesDeep = cosmosOf typeSubtypes

-- | Get all the direct child 'name a's of the given 'Term' from 'TyAbs'es.
termTyBinds :: Traversal' (Term tyname name ann) (tyname ann)
termTyBinds f = \case
    TyAbs ann tn k t -> f tn <&> \tn' -> TyAbs ann tn' k t
    x -> pure x

-- | Get all the direct child 'name a's of the given 'Term' from 'LamAbs'es.
termBinds :: Traversal' (Term tyname name ann) (name ann)
termBinds f = \case
    LamAbs ann n ty t -> f n <&> \n' -> LamAbs ann n' ty t
    x -> pure x

-- | Get all the direct child 'name a's of the given 'Term' from 'Var's.
termVars :: Traversal' (Term tyname name ann) (name ann)
termVars f = \case
    Var ann n -> Var ann <$> f n
    x -> pure x

{-# INLINE termSubtypes #-}
-- | Get all the direct child 'Type's of the given 'Term'.
termSubtypes :: Traversal' (Term tyname name ann) (Type tyname ann)
termSubtypes f = \case
    LamAbs ann n ty t -> LamAbs ann n <$> f ty <*> pure t
    TyInst ann t ty -> TyInst ann t <$> f ty
    IWrap ann ty1 ty2 t -> IWrap ann <$> f ty1 <*> f ty2 <*> pure t
    Error ann ty -> Error ann <$> f ty
    t@TyAbs {} -> pure t
    a@Apply {} -> pure a
    u@Unwrap {} -> pure u
    v@Var {} -> pure v
    c@Constant {} -> pure c
    b@Builtin {} -> pure b

-- | Get all the transitive child 'Type's of the given 'Term'.
termSubtypesDeep
    :: (Applicative f, Contravariant f)
    => LensLike' f (Term tyname name ann) (Type tyname ann)
termSubtypesDeep = termSubtermsDeep . termSubtypes . typeSubtypesDeep

{-# INLINE termSubterms #-}
-- | Get all the direct child 'Term's of the given 'Term'.
termSubterms :: Traversal' (Term tyname name ann) (Term tyname name ann)
termSubterms f = \case
    LamAbs ann n ty t -> LamAbs ann n ty <$> f t
    TyInst ann t ty -> TyInst ann <$> f t <*> pure ty
    IWrap ann ty1 ty2 t -> IWrap ann ty1 ty2 <$> f t
    TyAbs ann n k t -> TyAbs ann n k <$> f t
    Apply ann t1 t2 -> Apply ann <$> f t1 <*> f t2
    Unwrap ann t -> Unwrap ann <$> f t
    e@Error {} -> pure e
    v@Var {} -> pure v
    c@Constant {} -> pure c
    b@Builtin {} -> pure b

-- | Get all the transitive child 'Term's of the given 'Term'.
termSubtermsDeep
    :: (Applicative f, Contravariant f)
    => LensLike' f (Term tyname name ann) (Term tyname name ann)
termSubtermsDeep = cosmosOf termSubterms
