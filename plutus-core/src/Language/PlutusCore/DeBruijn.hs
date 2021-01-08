{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
-- | Support for using de Bruijn indices for term and type names.
module Language.PlutusCore.DeBruijn
    ( Index (..)
    , DeBruijn (..)
    , NamedDeBruijn (..)
    , TyDeBruijn (..)
    , NamedTyDeBruijn (..)
    , FreeVariableError (..)
    , AsFreeVariableError (..)
    , deBruijnTy
    , deBruijnTerm
    , deBruijnProgram
    , unDeBruijnTy
    , unDeBruijnTerm
    , unDeBruijnProgram
    , unNameDeBruijn
    , unNameTyDeBruijn
    ) where

import           Language.PlutusCore.DeBruijn.Internal

import           Language.PlutusCore.Core
import           Language.PlutusCore.Name
import           Language.PlutusCore.Quote

import           Control.Monad.Except
import           Control.Monad.Reader

import qualified Data.Bimap                            as BM

-- | Convert a 'Type' with 'TyName's into a 'Type' with 'NamedTyDeBruijn's.
deBruijnTy
    :: (AsFreeVariableError e, MonadError e m)
    => Type TyName uni ann -> m (Type NamedTyDeBruijn uni ann)
deBruijnTy = flip runReaderT (Levels 0 BM.empty) . deBruijnTyM

-- | Convert a 'Term' with 'TyName's and 'Name's into a 'Term' with 'NamedTyDeBruijn's and 'NamedDeBruijn's.
deBruijnTerm
    :: (AsFreeVariableError e, MonadError e m)
    => Term TyName Name uni fun ann -> m (Term NamedTyDeBruijn NamedDeBruijn uni fun ann)
deBruijnTerm = flip runReaderT (Levels 0 BM.empty) . deBruijnTermM

-- | Convert a 'Program' with 'TyName's and 'Name's into a 'Program' with 'NamedTyDeBruijn's and 'NamedDeBruijn's.
deBruijnProgram
    :: (AsFreeVariableError e, MonadError e m)
    => Program TyName Name uni fun ann -> m (Program NamedTyDeBruijn NamedDeBruijn uni fun ann)
deBruijnProgram (Program ann ver term) = Program ann ver <$> deBruijnTerm term

{- Note [De Bruijn conversion and recursion schemes]
These are quite repetitive, but we can't use a catamorphism for this, because
we are not only altering the recursive type, but also the name type parameters.
These are normally constant in a catamorphic application.
-}
deBruijnTyM
    :: (MonadReader Levels m, AsFreeVariableError e, MonadError e m)
    => Type TyName uni ann
    -> m (Type NamedTyDeBruijn uni ann)
deBruijnTyM = \case
    -- variable case
    TyVar ann n -> TyVar ann <$> tyNameToDeBruijn n
    -- binder cases
    TyForall ann tn k ty -> declareUnique tn $ do
        tn' <- tyNameToDeBruijn tn
        withScope $ TyForall ann tn' k <$> deBruijnTyM ty
    TyLam ann tn k ty -> declareUnique tn $ do
        tn' <- tyNameToDeBruijn tn
        withScope $ TyLam ann tn' k <$> deBruijnTyM ty
    -- boring recursive cases
    TyFun ann i o -> TyFun ann <$> deBruijnTyM i <*> deBruijnTyM o
    TyApp ann fun arg -> TyApp ann <$> deBruijnTyM fun <*> deBruijnTyM arg
    TyIFix ann pat arg -> TyIFix ann <$> deBruijnTyM pat <*> deBruijnTyM arg
    -- boring non-recursive cases
    TyBuiltin ann con -> pure $ TyBuiltin ann con

deBruijnTermM
    :: (MonadReader Levels m, AsFreeVariableError e, MonadError e m)
    => Term TyName Name uni fun ann
    -> m (Term NamedTyDeBruijn NamedDeBruijn uni fun ann)
deBruijnTermM = \case
    -- variable case
    Var ann n -> Var ann <$> nameToDeBruijn n
    -- binder cases
    TyAbs ann tn k t -> declareUnique tn $ do
        tn' <- tyNameToDeBruijn tn
        withScope $ TyAbs ann tn' k <$> deBruijnTermM t
    LamAbs ann n ty t -> declareUnique n $ do
        n' <- nameToDeBruijn n
        withScope $ LamAbs ann n' <$> deBruijnTyM ty <*> deBruijnTermM t
    -- boring recursive cases
    Apply ann t1 t2 -> Apply ann <$> deBruijnTermM t1 <*> deBruijnTermM t2
    TyInst ann t ty -> TyInst ann <$> deBruijnTermM t <*> deBruijnTyM ty
    Unwrap ann t -> Unwrap ann <$> deBruijnTermM t
    IWrap ann pat arg t -> IWrap ann <$> deBruijnTyM pat <*> deBruijnTyM arg <*> deBruijnTermM t
    Error ann ty -> Error ann <$> deBruijnTyM ty
    -- boring non-recursive cases
    Constant ann con -> pure $ Constant ann con
    Builtin ann bn -> pure $ Builtin ann bn

-- | Convert a 'Type' with 'NamedTyDeBruijn's into a 'Type' with 'TyName's.
unDeBruijnTy
    :: (MonadQuote m, AsFreeVariableError e, MonadError e m)
    => Type NamedTyDeBruijn uni ann -> m (Type TyName uni ann)
unDeBruijnTy = flip runReaderT (Levels 0 BM.empty) . unDeBruijnTyM

-- | Convert a 'Term' with 'NamedTyDeBruijn's and 'NamedDeBruijn's into a 'Term' with 'TyName's and 'Name's.
unDeBruijnTerm
    :: (MonadQuote m, AsFreeVariableError e, MonadError e m)
    => Term NamedTyDeBruijn NamedDeBruijn uni fun ann -> m (Term TyName Name uni fun ann)
unDeBruijnTerm = flip runReaderT (Levels 0 BM.empty) . unDeBruijnTermM

-- | Convert a 'Program' with 'NamedTyDeBruijn's and 'NamedDeBruijn's into a 'Program' with 'TyName's and 'Name's.
unDeBruijnProgram
    :: (MonadQuote m, AsFreeVariableError e, MonadError e m)
    => Program NamedTyDeBruijn NamedDeBruijn uni fun ann -> m (Program TyName Name uni fun ann)
unDeBruijnProgram (Program ann ver term) = Program ann ver <$> unDeBruijnTerm term

unDeBruijnTyM
    :: (MonadReader Levels m, MonadQuote m, AsFreeVariableError e, MonadError e m)
    => Type NamedTyDeBruijn uni ann
    -> m (Type TyName uni ann)
unDeBruijnTyM = \case
    -- variable case
    TyVar ann n -> TyVar ann <$> deBruijnToTyName n
    -- binder cases
    TyForall ann tn k ty -> declareIndex tn $ do
        tn' <- deBruijnToTyName tn
        withScope $ TyForall ann tn' k <$> unDeBruijnTyM ty
    TyLam ann tn k ty -> declareIndex tn $ do
        tn' <- deBruijnToTyName tn
        withScope $ TyLam ann tn' k <$> unDeBruijnTyM ty
    -- boring recursive cases
    TyFun ann i o -> TyFun ann <$> unDeBruijnTyM i <*> unDeBruijnTyM o
    TyApp ann fun arg -> TyApp ann <$> unDeBruijnTyM fun <*> unDeBruijnTyM arg
    TyIFix ann pat arg -> TyIFix ann <$> unDeBruijnTyM pat <*> unDeBruijnTyM arg
    -- boring non-recursive cases
    TyBuiltin ann con -> pure $ TyBuiltin ann con

unDeBruijnTermM
    :: (MonadReader Levels m, MonadQuote m, AsFreeVariableError e, MonadError e m)
    => Term NamedTyDeBruijn NamedDeBruijn uni fun ann
    -> m (Term TyName Name uni fun ann)
unDeBruijnTermM = \case
    -- variable case
    Var ann n -> Var ann <$> deBruijnToName n
    -- binder cases
    TyAbs ann tn k t -> declareIndex tn $ do
        tn' <- deBruijnToTyName tn
        withScope $ TyAbs ann tn' k <$> unDeBruijnTermM t
    LamAbs ann n ty t -> declareIndex n $ do
        n' <- deBruijnToName n
        withScope $ LamAbs ann n' <$> unDeBruijnTyM ty <*> unDeBruijnTermM t
    -- boring recursive cases
    Apply ann t1 t2 -> Apply ann <$> unDeBruijnTermM t1 <*> unDeBruijnTermM t2
    TyInst ann t ty -> TyInst ann <$> unDeBruijnTermM t <*> unDeBruijnTyM ty
    Unwrap ann t -> Unwrap ann <$> unDeBruijnTermM t
    IWrap ann pat arg t -> IWrap ann <$> unDeBruijnTyM pat <*> unDeBruijnTyM arg <*> unDeBruijnTermM t
    Error ann ty -> Error ann <$> unDeBruijnTyM ty
    -- boring non-recursive cases
    Constant ann con -> pure $ Constant ann con
    Builtin ann bn -> pure $ Builtin ann bn
