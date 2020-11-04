{-# LANGUAGE LambdaCase #-}
-- | Definition analysis for untyped Plutus Core.
-- This just adapts term-related code from Language.PlutusCore.Analysis.Definitions;
-- we just re-use the typed machinery to do the hard work here.
module Language.UntypedPlutusCore.Analysis.Definitions
    ( termDefs
    , runTermDefs
    ) where

import           Language.UntypedPlutusCore.Core

import           Language.PlutusCore.Analysis.Definitions (ScopeType (TermScope), UniqueInfos, addDef, addUsage)
import           Language.PlutusCore.Error
import           Language.PlutusCore.Name

import           Data.Functor.Foldable

import           Control.Monad.State
import           Control.Monad.Writer

termDefs
    :: (Ord ann,
        HasUnique name TermUnique,
        MonadState (UniqueInfos ann) m,
        MonadWriter [UniqueError ann] m)
    => Term name uni ann
    -> m ()
termDefs = cata $ \case
    VarF ann n           -> addUsage n ann TermScope
    LamAbsF ann n t      -> addDef n ann TermScope >> t
    x                    -> sequence_ x

runTermDefs
    :: (Ord ann,
        HasUnique name TermUnique,
        Monad m)
    => Term name uni ann
    -> m (UniqueInfos ann, [UniqueError ann])
runTermDefs = runWriterT . flip execStateT mempty . termDefs

