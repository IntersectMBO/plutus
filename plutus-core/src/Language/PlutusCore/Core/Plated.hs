{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}

module Language.PlutusCore.Core.Plated
    ( typeTyBinds
    , typeTyVars
    , typeUniques
    , typeSubtypes
    , typeSubtypesDeep
    , termTyBinds
    , termBinds
    , termVars
    , termUniques
    , termSubtypes
    , termSubtypesDeep
    , termSubterms
    , termSubtermsDeep
    , typeUniquesDeep
    , termUniquesDeep
    ) where

import           Language.PlutusCore.Core.Type
import           Language.PlutusCore.Name

import           Control.Lens

infixr 6 <^>

-- | Compose two folds to make them run in parallel. The results are concatenated.
(<^>) :: Fold s a -> Fold s a -> Fold s a
(f1 <^> f2) g s = f1 g s *> f2 g s

-- | Get all the direct child 'tyname a's of the given 'Type' from binders.
typeTyBinds :: Traversal' (Type tyname uni ann) tyname
typeTyBinds f = \case
    TyForall ann tn k ty -> f tn <&> \tn' -> TyForall ann tn' k ty
    TyLam ann tn k ty    -> f tn <&> \tn' -> TyLam ann tn' k ty
    x                    -> pure x

-- | Get all the direct child 'tyname a's of the given 'Type' from 'TyVar's.
typeTyVars :: Traversal' (Type tyname uni ann) tyname
typeTyVars f = \case
    TyVar ann n -> TyVar ann <$> f n
    x           -> pure x

-- | Get all the direct child 'Unique's of the given 'Type' from binders 'TyVar's.
typeUniques :: HasUniques (Type tyname uni ann) => Traversal' (Type tyname uni ann) Unique
typeUniques f = \case
    TyForall ann tn k ty -> theUnique f tn <&> \tn' -> TyForall ann tn' k ty
    TyLam ann tn k ty    -> theUnique f tn <&> \tn' -> TyLam ann tn' k ty
    TyVar ann n          -> theUnique f n <&> TyVar ann
    x                    -> pure x

{-# INLINE typeSubtypes #-}
-- | Get all the direct child 'Type's of the given 'Type'.
typeSubtypes :: Traversal' (Type tyname uni ann) (Type tyname uni ann)
typeSubtypes f = \case
    TyFun ann ty1 ty2    -> TyFun ann <$> f ty1 <*> f ty2
    TyIFix ann pat arg   -> TyIFix ann <$> f pat <*> f arg
    TyForall ann tn k ty -> TyForall ann tn k <$> f ty
    TyLam ann tn k ty    -> TyLam ann tn k <$> f ty
    TyApp ann ty1 ty2    -> TyApp ann <$> f ty1 <*> f ty2
    b@TyBuiltin {}       -> pure b
    v@TyVar {}           -> pure v

-- | Get all the transitive child 'Type's of the given 'Type'.
typeSubtypesDeep :: Fold (Type tyname uni ann) (Type tyname uni ann)
typeSubtypesDeep = cosmosOf typeSubtypes

-- | Get all the direct child 'tyname a's of the given 'Term' from 'TyAbs'es.
termTyBinds :: Traversal' (Term tyname name uni fun ann) tyname
termTyBinds f = \case
    TyAbs ann tn k t -> f tn <&> \tn' -> TyAbs ann tn' k t
    x                -> pure x

-- | Get all the direct child 'name a's of the given 'Term' from 'LamAbs'es.
termBinds :: Traversal' (Term tyname name uni fun ann) name
termBinds f = \case
    LamAbs ann n ty t -> f n <&> \n' -> LamAbs ann n' ty t
    x                 -> pure x

-- | Get all the direct child 'name a's of the given 'Term' from 'Var's.
termVars :: Traversal' (Term tyname name uni fun ann) name
termVars f = \case
    Var ann n -> Var ann <$> f n
    x         -> pure x

-- | Get all the direct child 'Unique's of the given 'Term' (including the type-level ones).
termUniques :: HasUniques (Term tyname name uni fun ann) => Traversal' (Term tyname name uni fun ann) Unique
termUniques f = \case
    TyAbs ann tn k t  -> theUnique f tn <&> \tn' -> TyAbs ann tn' k t
    LamAbs ann n ty t -> theUnique f n <&> \n' -> LamAbs ann n' ty t
    Var ann n         -> theUnique f n <&> Var ann
    x                 -> pure x

{-# INLINE termSubtypes #-}
-- | Get all the direct child 'Type's of the given 'Term'.
termSubtypes :: Traversal' (Term tyname name uni fun ann) (Type tyname uni ann)
termSubtypes f = \case
    LamAbs ann n ty t   -> LamAbs ann n <$> f ty <*> pure t
    TyInst ann t ty     -> TyInst ann t <$> f ty
    IWrap ann ty1 ty2 t -> IWrap ann <$> f ty1 <*> f ty2 <*> pure t
    Error ann ty        -> Error ann <$> f ty
    t@TyAbs {}          -> pure t
    a@Apply {}          -> pure a
    u@Unwrap {}         -> pure u
    v@Var {}            -> pure v
    c@Constant {}       -> pure c
    b@Builtin {}        -> pure b

-- | Get all the transitive child 'Type's of the given 'Term'.
termSubtypesDeep :: Fold (Term tyname name uni fun ann) (Type tyname uni ann)
termSubtypesDeep = termSubtermsDeep . termSubtypes . typeSubtypesDeep

{-# INLINE termSubterms #-}
-- | Get all the direct child 'Term's of the given 'Term'.
termSubterms :: Traversal' (Term tyname name uni fun ann) (Term tyname name uni fun ann)
termSubterms f = \case
    LamAbs ann n ty t   -> LamAbs ann n ty <$> f t
    TyInst ann t ty     -> TyInst ann <$> f t <*> pure ty
    IWrap ann ty1 ty2 t -> IWrap ann ty1 ty2 <$> f t
    TyAbs ann n k t     -> TyAbs ann n k <$> f t
    Apply ann t1 t2     -> Apply ann <$> f t1 <*> f t2
    Unwrap ann t        -> Unwrap ann <$> f t
    e@Error {}          -> pure e
    v@Var {}            -> pure v
    c@Constant {}       -> pure c
    b@Builtin {}        -> pure b

-- | Get all the transitive child 'Term's of the given 'Term'.
termSubtermsDeep :: Fold (Term tyname name uni fun ann) (Term tyname name uni fun ann)
termSubtermsDeep = cosmosOf termSubterms

-- | Get all the transitive child 'Unique's of the given 'Type'.
typeUniquesDeep :: HasUniques (Type tyname uni ann) => Fold (Type tyname uni ann) Unique
typeUniquesDeep = typeSubtypesDeep . typeUniques

-- | Get all the transitive child 'Unique's of the given 'Term' (including the type-level ones).
termUniquesDeep :: HasUniques (Term tyname name uni fun ann) => Fold (Term tyname name uni fun ann) Unique
termUniquesDeep = termSubtermsDeep . (termSubtypes . typeUniquesDeep <^> termUniques)
