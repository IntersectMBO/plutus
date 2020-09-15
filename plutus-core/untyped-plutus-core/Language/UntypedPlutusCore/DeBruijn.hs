{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
-- | Support for using de Bruijn indices for term names.
module Language.UntypedPlutusCore.DeBruijn
    ( Index (..)
    , DeBruijn (..)
    , TyDeBruijn (..)
    , FreeVariableError (..)
    , deBruijnTerm
    , deBruijnProgram
    , unDeBruijnTerm
    , unDeBruijnProgram
    ) where

import           Language.PlutusCore.DeBruijn.Internal

import           Language.PlutusCore.Name
import           Language.PlutusCore.Quote
import           Language.UntypedPlutusCore.Core

import           Control.Monad.Except
import           Control.Monad.Reader

import qualified Data.Bimap                            as BM

{- Note [Comparison with typed deBruijn conversion]
This module is just a boring port of the typed version.
-}

-- | Convert a 'Term' with 'TyName's and 'Name's into a 'Term' with 'TyDeBruijn's and 'DeBruijn's.
deBruijnTerm
    :: MonadError FreeVariableError m
    => Term Name uni ann -> m (Term DeBruijn uni ann)
deBruijnTerm = flip runReaderT (Levels 0 BM.empty) . deBruijnTermM

-- | Convert a 'Program' with 'TyName's and 'Name's into a 'Program' with 'TyDeBruijn's and 'DeBruijn's.
deBruijnProgram
    :: MonadError FreeVariableError m
    => Program Name uni ann -> m (Program DeBruijn uni ann)
deBruijnProgram (Program ann ver term) = Program ann ver <$> deBruijnTerm term

deBruijnTermM
    :: (MonadReader Levels m, MonadError FreeVariableError m)
    => Term Name uni ann
    -> m (Term DeBruijn uni ann)
deBruijnTermM = \case
    -- variable case
    Var ann n -> Var ann <$> nameToDeBruijn n
    -- binder cases
    LamAbs ann n t -> declareUnique n $ do
        n' <- nameToDeBruijn n
        withScope $ LamAbs ann n' <$> deBruijnTermM t
    -- boring recursive cases
    Apply ann t1 t2 -> Apply ann <$> deBruijnTermM t1 <*> deBruijnTermM t2
    Delay ann t -> Delay ann <$> deBruijnTermM t
    Force ann t -> Force ann <$> deBruijnTermM t
    -- boring non-recursive cases
    Constant ann con -> pure $ Constant ann con
    Builtin ann bn -> pure $ Builtin ann bn
    Error ann -> pure $ Error ann

-- | Convert a 'Term' with 'TyDeBruijn's and 'DeBruijn's into a 'Term' with 'TyName's and 'Name's.
unDeBruijnTerm
    :: (MonadQuote m, MonadError FreeVariableError m)
    => Term DeBruijn uni ann -> m (Term Name uni ann)
unDeBruijnTerm = flip runReaderT (Levels 0 BM.empty) . unDeBruijnTermM

-- | Convert a 'Program' with 'TyDeBruijn's and 'DeBruijn's into a 'Program' with 'TyName's and 'Name's.
unDeBruijnProgram
    :: (MonadQuote m, MonadError FreeVariableError m)
    => Program DeBruijn uni ann -> m (Program Name uni ann)
unDeBruijnProgram (Program ann ver term) = Program ann ver <$> unDeBruijnTerm term

unDeBruijnTermM
    :: (MonadReader Levels m, MonadQuote m, MonadError FreeVariableError m)
    => Term DeBruijn uni ann
    -> m (Term Name uni ann)
unDeBruijnTermM = \case
    -- variable case
    Var ann n -> Var ann <$> deBruijnToName n
    -- binder cases
    LamAbs ann n t -> declareIndex n $ do
        n' <- deBruijnToName n
        withScope $ LamAbs ann n' <$> unDeBruijnTermM t
    -- boring recursive cases
    Apply ann t1 t2 -> Apply ann <$> unDeBruijnTermM t1 <*> unDeBruijnTermM t2
    Delay ann t -> Delay ann <$> unDeBruijnTermM t
    Force ann t -> Force ann <$> unDeBruijnTermM t
    -- boring non-recursive cases
    Constant ann con -> pure $ Constant ann con
    Builtin ann bn -> pure $ Builtin ann bn
    Error ann -> pure $ Error ann
