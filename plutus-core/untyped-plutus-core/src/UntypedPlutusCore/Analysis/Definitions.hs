{-# LANGUAGE LambdaCase #-}
-- | Definition analysis for untyped Plutus Core.
-- This just adapts term-related code from PlutusCore.Analysis.Definitions;
-- we just re-use the typed machinery to do the hard work here.
module UntypedPlutusCore.Analysis.Definitions
    ( termDefs
    , runTermDefs
    ) where

import           UntypedPlutusCore.Core

import           PlutusCore.Analysis.Definitions (ScopeType (TermScope), UniqueInfos, addDef, addUsage)
import           PlutusCore.Error
import           PlutusCore.Name

import           Data.Functor.Foldable

import           Control.Monad.State
import           Control.Monad.Writer

termDefs
    :: (Ord ann,
        HasUnique name TermUnique,
        MonadState (UniqueInfos ann) m,
        MonadWriter [UniqueError ann] m)
    => Term name uni fun ann
    -> m ()
termDefs = cata $ \case
    VarF ann n      -> addUsage n ann TermScope
    LamAbsF ann n t -> addDef n ann TermScope >> t
    x               -> sequence_ x

runTermDefs
    :: (Ord ann,
        HasUnique name TermUnique,
        Monad m)
    => Term name uni fun ann
    -> m (UniqueInfos ann, [UniqueError ann])
runTermDefs = runWriterT . flip execStateT mempty . termDefs
