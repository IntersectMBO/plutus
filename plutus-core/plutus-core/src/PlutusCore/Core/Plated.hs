-- editorconfig-checker-disable-file
{-# LANGUAGE RankNTypes #-}

module PlutusCore.Core.Plated
  ( kindSubkinds
  , kindSubkindsDeep
  , tyVarDeclSubkinds
  , typeTyBinds
  , typeTyVars
  , typeUniques
  , typeSubkinds
  , typeSubtypes
  , typeSubtypesDeep
  , varDeclSubtypes
  , termConstants
  , termTyBinds
  , termBinds
  , termVars
  , termUniques
  , termSubkinds
  , termSubtypes
  , termSubtermsDeep
  , termSubtypesDeep
  , termConstantsDeep
  , termSubterms
  , typeUniquesDeep
  , termUniquesDeep
  ) where

import PlutusPrelude ((<^>))

import PlutusCore.Core.Type
import PlutusCore.Name.Unique

import Control.Lens
import Universe

kindSubkinds :: Traversal' (Kind ann) (Kind ann)
kindSubkinds f kind0 = case kind0 of
  KindArrow ann dom cod -> KindArrow ann <$> f dom <*> f cod
  Type {} -> pure kind0

kindSubkindsDeep :: Fold (Kind ann) (Kind ann)
kindSubkindsDeep = cosmosOf kindSubkinds

-- | Get all the direct child 'Kind's of the given 'TyVarDecl'.
tyVarDeclSubkinds :: Traversal' (TyVarDecl tyname a) (Kind a)
tyVarDeclSubkinds f (TyVarDecl a ty k) = TyVarDecl a ty <$> f k
{-# INLINE tyVarDeclSubkinds #-}

-- | Get all the direct child 'tyname a's of the given 'Type' from binders.
typeTyBinds :: Traversal' (Type tyname uni ann) tyname
typeTyBinds f ty0 = case ty0 of
  TyForall ann tn k ty -> f tn <&> \tn' -> TyForall ann tn' k ty
  TyLam ann tn k ty -> f tn <&> \tn' -> TyLam ann tn' k ty
  TyApp {} -> pure ty0
  TyIFix {} -> pure ty0
  TyFun {} -> pure ty0
  TyBuiltin {} -> pure ty0
  TyVar {} -> pure ty0
  TySOP {} -> pure ty0

-- | Get all the direct child 'tyname a's of the given 'Type' from 'TyVar's.
typeTyVars :: Traversal' (Type tyname uni ann) tyname
typeTyVars f ty0 = case ty0 of
  TyVar ann n -> TyVar ann <$> f n
  TyForall {} -> pure ty0
  TyLam {} -> pure ty0
  TyApp {} -> pure ty0
  TyIFix {} -> pure ty0
  TyFun {} -> pure ty0
  TyBuiltin {} -> pure ty0
  TySOP {} -> pure ty0

-- | Get all the direct child 'Unique's of the given 'Type' from binders 'TyVar's.
typeUniques :: HasUniques (Type tyname uni ann) => Traversal' (Type tyname uni ann) Unique
typeUniques f ty0 = case ty0 of
  TyForall ann tn k ty -> theUnique f tn <&> \tn' -> TyForall ann tn' k ty
  TyLam ann tn k ty -> theUnique f tn <&> \tn' -> TyLam ann tn' k ty
  TyVar ann n -> theUnique f n <&> TyVar ann
  TyApp {} -> pure ty0
  TyIFix {} -> pure ty0
  TyFun {} -> pure ty0
  TyBuiltin {} -> pure ty0
  TySOP {} -> pure ty0

-- | Get all the direct child 'Kind's of the given 'Type'.
typeSubkinds :: Traversal' (Type tyname uni ann) (Kind ann)
typeSubkinds f ty0 = case ty0 of
  TyForall ann tn k ty -> f k <&> \k' -> TyForall ann tn k' ty
  TyLam ann tn k ty -> f k <&> \k' -> TyLam ann tn k' ty
  TyApp {} -> pure ty0
  TyIFix {} -> pure ty0
  TyFun {} -> pure ty0
  TyBuiltin {} -> pure ty0
  TyVar {} -> pure ty0
  TySOP {} -> pure ty0
{-# INLINE typeSubkinds #-}

-- | Get all the direct child 'Type's of the given 'Type'.
typeSubtypes :: Traversal' (Type tyname uni ann) (Type tyname uni ann)
typeSubtypes f ty0 = case ty0 of
  TyFun ann ty1 ty2 -> TyFun ann <$> f ty1 <*> f ty2
  TyIFix ann pat arg -> TyIFix ann <$> f pat <*> f arg
  TyForall ann tn k ty -> TyForall ann tn k <$> f ty
  TyLam ann tn k ty -> TyLam ann tn k <$> f ty
  TyApp ann ty1 ty2 -> TyApp ann <$> f ty1 <*> f ty2
  TySOP ann tyls -> TySOP ann <$> (traverse . traverse) f tyls
  TyBuiltin {} -> pure ty0
  TyVar {} -> pure ty0
{-# INLINE typeSubtypes #-}

-- | Get all the transitive child 'Type's of the given 'Type'.
typeSubtypesDeep :: Fold (Type tyname uni ann) (Type tyname uni ann)
typeSubtypesDeep = cosmosOf typeSubtypes

-- | Get all the direct child 'Type's of the given 'VarDecl'.
varDeclSubtypes :: Traversal' (VarDecl tyname name uni a) (Type tyname uni a)
varDeclSubtypes f (VarDecl a n ty) = VarDecl a n <$> f ty
{-# INLINE varDeclSubtypes #-}

-- | Get all the direct constants of the given 'Term' from 'Constant's.
termConstants :: Traversal' (Term tyname name uni fun ann) (Some (ValueOf uni))
termConstants f term0 = case term0 of
  Constant ann val -> Constant ann <$> f val
  Var {} -> pure term0
  TyAbs {} -> pure term0
  LamAbs {} -> pure term0
  TyInst {} -> pure term0
  IWrap {} -> pure term0
  Error {} -> pure term0
  Apply {} -> pure term0
  Unwrap {} -> pure term0
  Builtin {} -> pure term0
  Constr {} -> pure term0
  Case {} -> pure term0

-- | Get all the direct child 'tyname a's of the given 'Term' from 'TyAbs'es.
termTyBinds :: Traversal' (Term tyname name uni fun ann) tyname
termTyBinds f term0 = case term0 of
  TyAbs ann tn k t -> f tn <&> \tn' -> TyAbs ann tn' k t
  Var {} -> pure term0
  LamAbs {} -> pure term0
  TyInst {} -> pure term0
  IWrap {} -> pure term0
  Error {} -> pure term0
  Apply {} -> pure term0
  Unwrap {} -> pure term0
  Constant {} -> pure term0
  Builtin {} -> pure term0
  Constr {} -> pure term0
  Case {} -> pure term0

-- | Get all the direct child 'name a's of the given 'Term' from 'LamAbs'es.
termBinds :: Traversal' (Term tyname name uni fun ann) name
termBinds f term0 = case term0 of
  LamAbs ann n ty t -> f n <&> \n' -> LamAbs ann n' ty t
  Var {} -> pure term0
  TyAbs {} -> pure term0
  TyInst {} -> pure term0
  IWrap {} -> pure term0
  Error {} -> pure term0
  Apply {} -> pure term0
  Unwrap {} -> pure term0
  Constant {} -> pure term0
  Builtin {} -> pure term0
  Constr {} -> pure term0
  Case {} -> pure term0

-- | Get all the direct child 'name a's of the given 'Term' from 'Var's.
termVars :: Traversal' (Term tyname name uni fun ann) name
termVars f term0 = case term0 of
  Var ann n -> Var ann <$> f n
  TyAbs {} -> pure term0
  LamAbs {} -> pure term0
  TyInst {} -> pure term0
  IWrap {} -> pure term0
  Error {} -> pure term0
  Apply {} -> pure term0
  Unwrap {} -> pure term0
  Constant {} -> pure term0
  Builtin {} -> pure term0
  Constr {} -> pure term0
  Case {} -> pure term0

-- | Get all the direct child 'Unique's of the given 'Term' (including the type-level ones).
termUniques :: HasUniques (Term tyname name uni fun ann) => Traversal' (Term tyname name uni fun ann) Unique
termUniques f term0 = case term0 of
  TyAbs ann tn k t -> theUnique f tn <&> \tn' -> TyAbs ann tn' k t
  LamAbs ann n ty t -> theUnique f n <&> \n' -> LamAbs ann n' ty t
  Var ann n -> theUnique f n <&> Var ann
  TyInst {} -> pure term0
  IWrap {} -> pure term0
  Error {} -> pure term0
  Apply {} -> pure term0
  Unwrap {} -> pure term0
  Constant {} -> pure term0
  Builtin {} -> pure term0
  Constr {} -> pure term0
  Case {} -> pure term0

-- | Get all the direct child 'Kind's of the given 'Term'.
termSubkinds :: Traversal' (Term tyname name uni fun ann) (Kind ann)
termSubkinds f term0 = case term0 of
  TyAbs ann n k t -> f k <&> \k' -> TyAbs ann n k' t
  LamAbs {} -> pure term0
  Var {} -> pure term0
  TyInst {} -> pure term0
  IWrap {} -> pure term0
  Error {} -> pure term0
  Apply {} -> pure term0
  Unwrap {} -> pure term0
  Constant {} -> pure term0
  Builtin {} -> pure term0
  Constr {} -> pure term0
  Case {} -> pure term0
{-# INLINE termSubkinds #-}

-- | Get all the direct child 'Type's of the given 'Term'.
termSubtypes :: Traversal' (Term tyname name uni fun ann) (Type tyname uni ann)
termSubtypes f term0 = case term0 of
  LamAbs ann n ty t -> LamAbs ann n <$> f ty <*> pure t
  TyInst ann t ty -> TyInst ann t <$> f ty
  IWrap ann ty1 ty2 t -> IWrap ann <$> f ty1 <*> f ty2 <*> pure t
  Error ann ty -> Error ann <$> f ty
  Constr ann ty i es -> Constr ann <$> f ty <*> pure i <*> pure es
  Case ann ty arg cs -> Case ann <$> f ty <*> pure arg <*> pure cs
  TyAbs {} -> pure term0
  Apply {} -> pure term0
  Unwrap {} -> pure term0
  Var {} -> pure term0
  Constant {} -> pure term0
  Builtin {} -> pure term0
{-# INLINE termSubtypes #-}

-- | Get all the transitive child 'Constant's of the given 'Term'.
termConstantsDeep :: Fold (Term tyname name uni fun ann) (Some (ValueOf uni))
termConstantsDeep = termSubtermsDeep . termConstants

-- | Get all the transitive child 'Type's of the given 'Term'.
termSubtypesDeep :: Fold (Term tyname name uni fun ann) (Type tyname uni ann)
termSubtypesDeep = termSubtermsDeep . termSubtypes . typeSubtypesDeep

-- | Get all the direct child 'Term's of the given 'Term'.
termSubterms :: Traversal' (Term tyname name uni fun ann) (Term tyname name uni fun ann)
termSubterms f term0 = case term0 of
  LamAbs ann n ty t -> LamAbs ann n ty <$> f t
  TyInst ann t ty -> TyInst ann <$> f t <*> pure ty
  IWrap ann ty1 ty2 t -> IWrap ann ty1 ty2 <$> f t
  TyAbs ann n k t -> TyAbs ann n k <$> f t
  Apply ann t1 t2 -> Apply ann <$> f t1 <*> f t2
  Unwrap ann t -> Unwrap ann <$> f t
  Constr ann ty i es -> Constr ann ty i <$> traverse f es
  Case ann ty arg cs -> Case ann ty <$> f arg <*> traverse f cs
  Error {} -> pure term0
  Var {} -> pure term0
  Constant {} -> pure term0
  Builtin {} -> pure term0
{-# INLINE termSubterms #-}

-- | Get all the transitive child 'Term's of the given 'Term'.
termSubtermsDeep :: Fold (Term tyname name uni fun ann) (Term tyname name uni fun ann)
termSubtermsDeep = cosmosOf termSubterms

-- | Get all the transitive child 'Unique's of the given 'Type'.
typeUniquesDeep :: HasUniques (Type tyname uni ann) => Fold (Type tyname uni ann) Unique
typeUniquesDeep = typeSubtypesDeep . typeUniques

-- | Get all the transitive child 'Unique's of the given 'Term' (including the type-level ones).
termUniquesDeep :: HasUniques (Term tyname name uni fun ann) => Fold (Term tyname name uni fun ann) Unique
termUniquesDeep = termSubtermsDeep . (termSubtypes . typeUniquesDeep <^> termUniques)
