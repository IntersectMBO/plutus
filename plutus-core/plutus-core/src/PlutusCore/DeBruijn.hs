{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}

-- | Support for using de Bruijn indices for term and type names.
module PlutusCore.DeBruijn
  ( Index (..)
  , Level (..)
  , LevelInfo (..)
  , HasIndex (..)
  , DeBruijn (..)
  , NamedDeBruijn (..)
  -- we follow the same approach as Renamed, expose the constructor from Internal module,
  -- but hide it in this parent module.
  , FakeNamedDeBruijn (unFakeNamedDeBruijn)
  , TyDeBruijn (..)
  , NamedTyDeBruijn (..)
  , FreeVariableError (..)
  , unNameDeBruijn
  , unNameTyDeBruijn
  , fakeNameDeBruijn
  , fakeTyNameDeBruijn
  , deBruijnTy
  , deBruijnTerm
  , unDeBruijnTy
  , unDeBruijnTerm

    -- * unsafe api, use with care
  , deBruijnTyWith
  , deBruijnTermWith
  , unDeBruijnTyWith
  , unDeBruijnTermWith
  , freeIndexAsConsistentLevel
  , deBruijnInitIndex
  , fromFake
  , toFake
  ) where

import PlutusCore.DeBruijn.Internal

import PlutusCore.Core.Type
import PlutusCore.Name.Unique
import PlutusCore.Quote

import Control.Lens hiding (Index, Level, index)
import Control.Monad.Except
import Control.Monad.Reader

{- Note [DeBruijn indices of Binders]
In a debruijnijfied Term AST, the Binders have a debruijn index
at their the specific AST location.
During *undebruijnification* we ignore such binders' indices because they are meaningless,
and instead use the convention that such introduced binders have
a fixed debruijn index '0' at their introduction.
-}

-- | Takes a "handler" function to execute when encountering free variables.
unDeBruijnTyWith
  :: MonadQuote m
  => (Index -> ReaderT LevelInfo m Unique)
  -> Type NamedTyDeBruijn uni ann
  -> m (Type TyName uni ann)
unDeBruijnTyWith = (runDeBruijnT .) . unDeBruijnTyWithM

-- | Takes a "handler" function to execute when encountering free variables.
unDeBruijnTermWith
  :: MonadQuote m
  => (Index -> ReaderT LevelInfo m Unique)
  -> Term NamedTyDeBruijn NamedDeBruijn uni fun ann
  -> m (Term TyName Name uni fun ann)
unDeBruijnTermWith = (runDeBruijnT .) . unDeBruijnTermWithM

{-| Convert a 'Type' with 'NamedTyDeBruijn's into a 'Type' with 'TyName's.
Will throw an error if a free variable is encountered. -}
unDeBruijnTy
  :: (MonadQuote m, MonadError FreeVariableError m)
  => Type NamedTyDeBruijn uni ann -> m (Type TyName uni ann)
unDeBruijnTy = unDeBruijnTyWith freeIndexThrow

{-| Convert a 'Term' with 'NamedTyDeBruijn's and 'NamedDeBruijn's into a 'Term' with 'TyName's and
 'Name's. Will throw an error if a free variable is encountered. -}
unDeBruijnTerm
  :: (MonadQuote m, MonadError FreeVariableError m)
  => Term NamedTyDeBruijn NamedDeBruijn uni fun ann -> m (Term TyName Name uni fun ann)
unDeBruijnTerm = unDeBruijnTermWith freeIndexThrow

{-| Convert a 'Type' with 'TyName's into a 'Type' with 'NamedTyDeBruijn's.
Will throw an error if a free variable is encountered. -}
deBruijnTy
  :: MonadError FreeVariableError m
  => Type TyName uni ann -> m (Type NamedTyDeBruijn uni ann)
deBruijnTy = deBruijnTyWith freeUniqueThrow

{-| Convert a 'Term' with 'TyName's and 'Name's into a 'Term' with 'NamedTyDeBruijn's and
'NamedDeBruijn's. Will throw an error if a free variable is encountered. -}
deBruijnTerm
  :: MonadError FreeVariableError m
  => Term TyName Name uni fun ann -> m (Term NamedTyDeBruijn NamedDeBruijn uni fun ann)
deBruijnTerm = deBruijnTermWith freeUniqueThrow

deBruijnTermWith
  :: Monad m
  => (Unique -> ReaderT LevelInfo m Index)
  -> Term TyName Name uni fun ann
  -> m (Term NamedTyDeBruijn NamedDeBruijn uni fun ann)
deBruijnTermWith = (runDeBruijnT .) . deBruijnTermWithM

deBruijnTyWith
  :: Monad m
  => (Unique -> ReaderT LevelInfo m Index)
  -> Type TyName uni ann
  -> m (Type NamedTyDeBruijn uni ann)
deBruijnTyWith = (runDeBruijnT .) . deBruijnTyWithM

{- Note [De Bruijn conversion and recursion schemes]
These are quite repetitive, but we can't use a catamorphism for this, because
we are not only altering the recursive type, but also the name type parameters.
These are normally constant in a catamorphic application.
-}

deBruijnTyWithM
  :: forall m uni ann
   . MonadReader LevelInfo m
  => (Unique -> m Index)
  -> Type TyName uni ann
  -> m (Type NamedTyDeBruijn uni ann)
deBruijnTyWithM h = go
  where
    go :: Type TyName uni ann -> m (Type NamedTyDeBruijn uni ann)
    go = \case
      -- variable case
      TyVar ann n -> TyVar ann <$> tyNameToDeBruijn h n
      -- binder cases
      TyForall ann tn k ty -> declareUnique tn $ do
        tn' <- tyNameToDeBruijn h tn
        withScope $ TyForall ann tn' k <$> go ty
      TyLam ann tn k ty -> declareUnique tn $ do
        tn' <- tyNameToDeBruijn h tn
        withScope $ TyLam ann tn' k <$> go ty
      -- boring recursive cases
      TyFun ann i o -> TyFun ann <$> go i <*> go o
      TyApp ann fun arg -> TyApp ann <$> go fun <*> go arg
      TyIFix ann pat arg -> TyIFix ann <$> go pat <*> go arg
      TySOP ann tyls -> TySOP ann <$> (traverse . traverse) go tyls
      -- boring non-recursive cases
      TyBuiltin ann someUni -> pure $ TyBuiltin ann someUni

deBruijnTermWithM
  :: forall m uni fun ann
   . MonadReader LevelInfo m
  => (Unique -> m Index)
  -> Term TyName Name uni fun ann
  -> m (Term NamedTyDeBruijn NamedDeBruijn uni fun ann)
deBruijnTermWithM h = go
  where
    goT :: Type TyName uni ann -> m (Type NamedTyDeBruijn uni ann)
    goT = deBruijnTyWithM h

    go :: Term TyName Name uni fun ann -> m (Term NamedTyDeBruijn NamedDeBruijn uni fun ann)
    go = \case
      -- variable case
      Var ann n -> Var ann <$> nameToDeBruijn h n
      -- binder cases
      TyAbs ann tn k t -> declareUnique tn $ do
        tn' <- tyNameToDeBruijn h tn
        withScope $ TyAbs ann tn' k <$> go t
      LamAbs ann n ty t -> declareUnique n $ do
        n' <- nameToDeBruijn h n
        withScope $ LamAbs ann n' <$> goT ty <*> go t
      -- boring recursive cases
      Apply ann t1 t2 -> Apply ann <$> go t1 <*> go t2
      TyInst ann t ty -> TyInst ann <$> go t <*> goT ty
      Unwrap ann t -> Unwrap ann <$> go t
      IWrap ann pat arg t -> IWrap ann <$> goT pat <*> goT arg <*> go t
      Error ann ty -> Error ann <$> goT ty
      Constr ann ty i es -> Constr ann <$> goT ty <*> pure i <*> traverse go es
      Case ann ty arg cs -> Case ann <$> goT ty <*> go arg <*> traverse go cs
      -- boring non-recursive cases
      Constant ann con -> pure $ Constant ann con
      Builtin ann bn -> pure $ Builtin ann bn

-- | Takes a "handler" function to execute when encountering free variables.
unDeBruijnTyWithM
  :: forall m uni ann
   . (MonadReader LevelInfo m, MonadQuote m)
  => (Index -> m Unique)
  -> Type NamedTyDeBruijn uni ann
  -> m (Type TyName uni ann)
unDeBruijnTyWithM h = go
  where
    go :: Type NamedTyDeBruijn uni ann -> m (Type TyName uni ann)
    go = \case
      -- variable case
      TyVar ann n -> TyVar ann <$> deBruijnToTyName h n
      -- binder cases
      TyForall ann tn k ty ->
        -- See Note [DeBruijn indices of Binders]
        declareBinder $ do
          tn' <- deBruijnToTyName h $ set index deBruijnInitIndex tn
          withScope $ TyForall ann tn' k <$> go ty
      TyLam ann tn k ty ->
        -- See Note [DeBruijn indices of Binders]
        declareBinder $ do
          tn' <- deBruijnToTyName h $ set index deBruijnInitIndex tn
          withScope $ TyLam ann tn' k <$> go ty
      -- boring recursive cases
      TyFun ann i o -> TyFun ann <$> go i <*> go o
      TyApp ann fun arg -> TyApp ann <$> go fun <*> go arg
      TyIFix ann pat arg -> TyIFix ann <$> go pat <*> go arg
      TySOP ann tyls -> TySOP ann <$> (traverse . traverse) go tyls
      -- boring non-recursive cases
      TyBuiltin ann someUni -> pure $ TyBuiltin ann someUni

-- | Takes a "handler" function to execute when encountering free variables.
unDeBruijnTermWithM
  :: forall m uni fun ann
   . (MonadReader LevelInfo m, MonadQuote m)
  => (Index -> m Unique)
  -> Term NamedTyDeBruijn NamedDeBruijn uni fun ann
  -> m (Term TyName Name uni fun ann)
unDeBruijnTermWithM h = go
  where
    goT :: Type NamedTyDeBruijn uni ann -> m (Type TyName uni ann)
    goT = unDeBruijnTyWithM h

    go :: Term NamedTyDeBruijn NamedDeBruijn uni fun ann -> m (Term TyName Name uni fun ann)
    go = \case
      -- variable case
      Var ann n -> Var ann <$> deBruijnToName h n
      -- binder cases
      TyAbs ann tn k t ->
        -- See Note [DeBruijn indices of Binders]
        declareBinder $ do
          tn' <- deBruijnToTyName h $ set index deBruijnInitIndex tn
          withScope $ TyAbs ann tn' k <$> go t
      LamAbs ann n ty t ->
        -- See Note [DeBruijn indices of Binders]
        declareBinder $ do
          n' <- deBruijnToName h $ set index deBruijnInitIndex n
          withScope $ LamAbs ann n' <$> goT ty <*> go t
      -- boring recursive cases
      Apply ann t1 t2 -> Apply ann <$> go t1 <*> go t2
      TyInst ann t ty -> TyInst ann <$> go t <*> goT ty
      Unwrap ann t -> Unwrap ann <$> go t
      IWrap ann pat arg t -> IWrap ann <$> goT pat <*> goT arg <*> go t
      Error ann ty -> Error ann <$> goT ty
      Constr ann ty i es -> Constr ann <$> goT ty <*> pure i <*> traverse go es
      Case ann ty arg cs -> Case ann <$> goT ty <*> go arg <*> traverse go cs
      -- boring non-recursive cases
      Constant ann con -> pure $ Constant ann con
      Builtin ann bn -> pure $ Builtin ann bn
