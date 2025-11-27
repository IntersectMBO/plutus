{-# LANGUAGE LambdaCase #-}

{-| Definition analysis for untyped Plutus Core.
This just adapts term-related code from PlutusCore.Analysis.Definitions;
we just re-use the typed machinery to do the hard work here. -}
module UntypedPlutusCore.Analysis.Definitions
  ( termDefs
  , runTermDefs
  ) where

import UntypedPlutusCore.Core

import PlutusCore.Analysis.Definitions (ScopeType (TermScope), UniqueInfos, addDef, addUsage)
import PlutusCore.Error (UniqueError)
import PlutusCore.Name.Unique (HasUnique, TermUnique (TermUnique), Unique (Unique))

import Control.Lens (forMOf_)
import Control.Monad.State (MonadState, execStateT)
import Control.Monad.Writer (MonadWriter, WriterT (runWriterT))

{-| Given a UPLC term, add all of its term definitions and usages, including its subterms,
to a global map. -}
termDefs
  :: ( Ord ann
     , HasUnique name TermUnique
     , MonadState (UniqueInfos ann) m
     , MonadWriter [UniqueError ann] m
     )
  => Term name uni fun ann
  -> m ()
termDefs tm = do
  forMOf_ termSubtermsDeep tm handleTerm

handleTerm
  :: ( Ord ann
     , HasUnique name TermUnique
     , MonadState (UniqueInfos ann) m
     , MonadWriter [UniqueError ann] m
     )
  => Term name uni fun ann
  -> m ()
handleTerm = \case
  Var ann n ->
    addUsage n ann TermScope
  LamAbs ann n _ ->
    addDef n ann TermScope
  _ -> pure ()

runTermDefs
  :: ( Ord ann
     , HasUnique name TermUnique
     , Monad m
     )
  => Term name uni fun ann
  -> m (UniqueInfos ann, [UniqueError ann])
runTermDefs = runWriterT . flip execStateT mempty . termDefs
