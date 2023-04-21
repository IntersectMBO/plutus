-- | Definition analysis for untyped Plutus Core.
-- This just adapts term-related code from PlutusCore.Analysis.Definitions;
-- we just re-use the typed machinery to do the hard work here.
module UntypedPlutusCore.Analysis.Definitions
    ( termDefs
    , runTermDefs
    ) where

import UntypedPlutusCore.Core

import PlutusCore.Analysis.Definitions (ScopeType (TermScope), UniqueInfos, addDef, addUsage)
import PlutusCore.Error (UniqueError)
import PlutusCore.Name (HasUnique, TermUnique (TermUnique), Unique (Unique))

import Control.Lens (forMOf)
import Control.Monad.State (MonadState, execStateT)
import Control.Monad.Writer (MonadWriter, WriterT (runWriterT))

termDefs
    :: (Ord ann,
        HasUnique name TermUnique,
        MonadState (UniqueInfos ann) m,
        MonadWriter [UniqueError ann] m)
    => Term name uni fun ann
    -> m (Term name uni fun ann)
termDefs tm = case tm of
    Var ann n      -> do
        addUsage n ann TermScope
        pure tm
    LamAbs ann n t -> do
        addDef n ann TermScope
        termDefs t
    x               -> forMOf termSubterms x termDefs

runTermDefs
    :: (Ord ann,
        HasUnique name TermUnique,
        Monad m)
    => Term name uni fun ann
    -> m (UniqueInfos ann, [UniqueError ann])
runTermDefs = runWriterT . flip execStateT mempty . termDefs
