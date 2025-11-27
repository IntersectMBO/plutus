{-# LANGUAGE LambdaCase #-}

-- | Definition analysis for Plutus Core.
module PlutusCore.Analysis.Definitions
  ( UniqueInfos
  , ScopeType (..)
  , termDefs
  , handleType
  , runTermDefs
  , addDef
  , addUsage
  ) where

import PlutusCore.Core.Plated (termSubtermsDeep, termSubtypesDeep)
import PlutusCore.Core.Type (Term (LamAbs, TyAbs, Var), Type (TyForall, TyLam, TyVar))
import PlutusCore.Error (UniqueError (..))
import PlutusCore.Name.Unique
  ( HasUnique
  , TermUnique (TermUnique)
  , TypeUnique (TypeUnique)
  , Unique (Unique)
  , theUnique
  )
import PlutusCore.Name.UniqueMap (UniqueMap, insertByNameIndex, lookupNameIndex)

import Control.Lens (forMOf_, (^.))
import Control.Monad (when)
import Control.Monad.State (MonadState, execStateT, gets, modify)
import Control.Monad.Writer (MonadWriter, runWriterT, tell)

import Data.Foldable (for_)
import Data.Set qualified as Set

{- Note [Unique usage errors]
The definitions analysis can find a number of problems with usage of uniques, however
clients may not always want to throw an error on all of them, hence we simply return
them all and allow the client to chose if they want to throw some of them.
-}

-- | Information about a unique, a pair of a definition if we have one and a set of uses.
type UniqueInfo ann = (Maybe (ScopedLoc ann), Set.Set (ScopedLoc ann))

type UniqueInfos ann = UniqueMap Unique (UniqueInfo ann)

data ScopedLoc ann = ScopedLoc ScopeType ann deriving stock (Eq, Ord)

{-| Tag for distinguishing between whether we are talking about the term scope
for variables or the type scope for variables. -}
data ScopeType = TermScope | TypeScope deriving stock (Eq, Ord)

lookupDef
  :: ( Ord ann
     , HasUnique name unique
     , MonadState (UniqueInfos ann) m
     )
  => name
  -> m (UniqueInfo ann)
lookupDef n = do
  previousDef <- gets $ lookupNameIndex n
  case previousDef of
    Just d -> pure d
    Nothing -> do
      let empty = (Nothing, mempty)
      modify $ insertByNameIndex n empty
      pure empty

addDef
  :: ( Ord ann
     , HasUnique n unique
     , MonadState (UniqueInfos ann) m
     , MonadWriter [UniqueError ann] m
     )
  => n
  -- ^ The variable
  -> ann
  -- ^ The annotation of the variable
  -> ScopeType
  -- ^ The scope type
  -> m ()
addDef n newDef tpe = do
  let def = ScopedLoc tpe newDef

  d@(_, uses) <- lookupDef n
  checkUndefined n def d
  modify $ insertByNameIndex n (Just def, uses)

-- | Check that a variable is currently undefined.
checkUndefined
  :: ( HasUnique n u
     , MonadState (UniqueInfos ann) m
     , MonadWriter [UniqueError ann] m
     )
  => n
  -- ^ The variable
  -> ScopedLoc ann
  -- ^ The new definition
  -> UniqueInfo ann
  -- ^ The existing info
  -> m ()
checkUndefined n (ScopedLoc _ newDef) info = case info of
  (Just (ScopedLoc _ prevDef), _) -> tell [MultiplyDefined (n ^. theUnique) prevDef newDef]
  _ -> pure ()

addUsage
  :: ( Ord ann
     , HasUnique n unique
     , MonadState (UniqueInfos ann) m
     , MonadWriter [UniqueError ann] m
     )
  => n
  -- ^ The variable
  -> ann
  -- ^ The annotation of the variable
  -> ScopeType
  -- ^ The scope type
  -> m ()
addUsage n newUse tpe = do
  let use = ScopedLoc tpe newUse

  d@(def, uses) <- lookupDef n
  checkCoherency n use d
  checkDefined n use d
  modify $ insertByNameIndex n (def, Set.insert use uses)

checkDefined
  :: ( HasUnique n u
     , MonadWriter [UniqueError ann] m
     )
  => n
  -- ^ The variable
  -> ScopedLoc ann
  -- ^ The new definition
  -> UniqueInfo ann
  -- ^ The existing info
  -> m ()
checkDefined n (ScopedLoc _ loc) (def, _) = case def of
  Nothing -> tell [FreeVariable (n ^. theUnique) loc]
  Just _ -> pure ()

checkCoherency
  :: ( HasUnique n u
     , MonadWriter [UniqueError ann] m
     )
  => n
  -- ^ The variable
  -> ScopedLoc ann
  -- ^ The new definition
  -> UniqueInfo ann
  -- ^ The existing info
  -> m ()
checkCoherency n (ScopedLoc tpe loc) (def, uses) = do
  for_ def checkLoc
  for_ (Set.toList uses) checkLoc
  where
    checkLoc (ScopedLoc tpe' loc') =
      when (tpe' /= tpe) $
        tell [IncoherentUsage (n ^. theUnique) loc' loc]

{-| Given a PLC term, add all of its term and type definitions and usages, including its subterms
and subtypes, to a global map. -}
termDefs
  :: ( Ord ann
     , HasUnique name TermUnique
     , HasUnique tyname TypeUnique
     , MonadState (UniqueInfos ann) m
     , MonadWriter [UniqueError ann] m
     )
  => Term tyname name uni fun ann
  -> m ()
termDefs tm = do
  forMOf_ termSubtermsDeep tm handleTerm
  forMOf_ termSubtypesDeep tm handleType

handleTerm
  :: ( Ord ann
     , HasUnique name TermUnique
     , HasUnique tyname TypeUnique
     , MonadState (UniqueInfos ann) m
     , MonadWriter [UniqueError ann] m
     )
  => Term tyname name uni fun ann
  -> m ()
handleTerm = \case
  Var ann n ->
    addUsage n ann TermScope
  LamAbs ann n _ _ -> do
    addDef n ann TermScope
  TyAbs ann tn _ _ -> do
    addDef tn ann TypeScope
  _ -> pure ()

-- | Given a type, add its type definition/usage, including its subtypes, to a global map.
handleType
  :: ( Ord ann
     , HasUnique tyname TypeUnique
     , MonadState (UniqueInfos ann) m
     , MonadWriter [UniqueError ann] m
     )
  => Type tyname uni ann
  -> m ()
handleType = \case
  TyVar ann n ->
    addUsage n ann TypeScope
  TyForall ann tn _ _ ->
    addDef tn ann TypeScope
  TyLam ann tn _ _ ->
    addDef tn ann TypeScope
  _ -> pure ()

runTermDefs
  :: ( Ord ann
     , HasUnique name TermUnique
     , HasUnique tyname TypeUnique
     , Monad m
     )
  => Term tyname name uni fun ann
  -> m (UniqueInfos ann, [UniqueError ann])
runTermDefs = runWriterT . flip execStateT mempty . termDefs
