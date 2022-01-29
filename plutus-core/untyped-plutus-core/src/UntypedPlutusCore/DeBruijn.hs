{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
-- | Support for using de Bruijn indices for term names.
module UntypedPlutusCore.DeBruijn
    ( Index (..)
    , HasIndex (..)
    , DeBruijn (..)
    , NamedDeBruijn (..)
    , FreeVariableError (..)
    , AsFreeVariableError (..)
    , deBruijnTerm
    , deBruijnProgram
    , unDeBruijnTerm
    , unDeBruijnProgram
    , unNameDeBruijn
    , fakeNameDeBruijn
    -- * unsafe api, use with care
    , deBruijnTermWith
    , deBruijnProgramWith
    , unDeBruijnTermWith
    , unDeBruijnProgramWith
    , freeIndexAsConsistentLevel
    ) where

import PlutusCore.DeBruijn.Internal

import PlutusCore.Name
import PlutusCore.Quote
import UntypedPlutusCore.Core

import Control.Lens hiding (Index, Level, index)
import Control.Monad.Except
import Control.Monad.Reader

{- Note [Comparison with typed deBruijn conversion]
This module is just a boring port of the typed version.
-}

-- | Convert a 'Term' with 'Name's into a 'Term' with 'DeBruijn's.
-- Will throw an error if a free variable is encountered.
deBruijnTerm
    :: (AsFreeVariableError e, MonadError e m)
    => Term Name uni fun ann -> m (Term NamedDeBruijn uni fun ann)
deBruijnTerm = deBruijnTermWith freeUniqueThrow

-- | Convert a 'Program' with Name's into a 'Program' with 'DeBruijn's.
-- Will throw an error if a free variable is encountered.
deBruijnProgram
    :: (AsFreeVariableError e, MonadError e m)
    => Program Name uni fun ann -> m (Program NamedDeBruijn uni fun ann)
deBruijnProgram = deBruijnProgramWith freeUniqueThrow

-- | Takes a "handler" function to execute when encountering free variables.
deBruijnProgramWith
    :: Monad m
    => (Unique -> ReaderT Levels m Index)
    -> Program Name uni fun ann
    -> m (Program NamedDeBruijn uni fun ann)
deBruijnProgramWith h (Program ann ver term) = Program ann ver <$> deBruijnTermWith h term

-- | Convert a 'Term' with 'DeBruijn's into a 'Term' with 'Name's.
-- Will throw an error if a free variable is encountered.
unDeBruijnTerm
    :: (MonadQuote m, AsFreeVariableError e, MonadError e m)
    => Term NamedDeBruijn uni fun ann -> m (Term Name uni fun ann)
unDeBruijnTerm = unDeBruijnTermWith freeIndexThrow

-- | Convert a 'Program' with 'DeBruijn's into a 'Program' with 'Name's.
-- Will throw an error if a free variable is encountered.
unDeBruijnProgram
    :: (MonadQuote m, AsFreeVariableError e, MonadError e m)
    => Program NamedDeBruijn uni fun ann -> m (Program Name uni fun ann)
unDeBruijnProgram = unDeBruijnProgramWith freeIndexThrow

-- | Takes a "handler" function to execute when encountering free variables.
unDeBruijnProgramWith
    :: MonadQuote m
    => (Index -> ReaderT Levels m Unique)
    -> Program NamedDeBruijn uni fun ann
    -> m (Program Name uni fun ann)
unDeBruijnProgramWith h (Program ann ver term) = Program ann ver <$> unDeBruijnTermWith h term

deBruijnTermWith
    :: Monad m
    => (Unique -> ReaderT Levels m Index)
    -> Term Name uni fun ann
    -> m (Term NamedDeBruijn uni fun ann)
deBruijnTermWith = (runDeBruijnT .) . deBruijnTermWithM

-- | Takes a "handler" function to execute when encountering free variables.
unDeBruijnTermWith
    :: MonadQuote m
    => (Index -> ReaderT Levels m Unique)
    -> Term NamedDeBruijn uni fun ann
    -> m (Term Name uni fun ann)
unDeBruijnTermWith = (runDeBruijnT .) . unDeBruijnTermWithM

deBruijnTermWithM
    :: MonadReader Levels m
    => (Unique -> m Index)
    -> Term Name uni fun ann
    -> m (Term NamedDeBruijn uni fun ann)
deBruijnTermWithM h = go
 where
   go = \case
       -- variable case
       Var ann n -> Var ann <$> nameToDeBruijn h n
       -- binder cases
       LamAbs ann n t -> declareUnique n $ do
           n' <- nameToDeBruijn h n
           withScope $ LamAbs ann n' <$> go t
       -- boring recursive cases
       Apply ann t1 t2 -> Apply ann <$> go t1 <*> go t2
       Delay ann t -> Delay ann <$> go t
       Force ann t -> Force ann <$> go t
       -- boring non-recursive cases
       Constant ann con -> pure $ Constant ann con
       Builtin ann bn -> pure $ Builtin ann bn
       Error ann -> pure $ Error ann

-- | Takes a "handler" function to execute when encountering free variables.
unDeBruijnTermWithM
    :: (MonadReader Levels m, MonadQuote m)
    => (Index -> m Unique)
    -> Term NamedDeBruijn uni fun ann
    -> m (Term Name uni fun ann)
unDeBruijnTermWithM h = go
  where
    go = \case
        -- variable case
        Var ann n -> Var ann <$> deBruijnToName h n
        -- binder cases
        LamAbs ann n t ->
            -- See NOTE: [DeBruijn indices of Binders]
            declareBinder $ do
              n' <- deBruijnToName h $ set index 0 n
              withScope $ LamAbs ann n' <$> go t
        -- boring recursive cases
        Apply ann t1 t2 -> Apply ann <$> go t1 <*> go t2
        Delay ann t -> Delay ann <$> go t
        Force ann t -> Force ann <$> go t
        -- boring non-recursive cases
        Constant ann con -> pure $ Constant ann con
        Builtin ann bn -> pure $ Builtin ann bn
        Error ann -> pure $ Error ann
