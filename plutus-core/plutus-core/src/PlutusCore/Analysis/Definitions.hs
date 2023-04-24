-- | Definition analysis for Plutus Core.
module PlutusCore.Analysis.Definitions
    ( UniqueInfos
    , ScopeType(..)
    , termDefs
    , typeDefs
    , runTermDefs
    , runTypeDefs
    , addDef
    , addUsage
    ) where

import PlutusCore.Core
import PlutusCore.Error
import PlutusCore.Name


import Control.Lens (forMOf, (^.))
import Control.Monad.Except
import Control.Monad.State
import Control.Monad.Writer

import Data.Foldable
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

-- | Tag for distinguishing between whether we are talking about the term scope
-- for variables or the type scope for variables.
data ScopeType = TermScope | TypeScope deriving stock (Eq, Ord)

lookupDef
    :: (Ord ann,
        HasUnique name unique,
        MonadState (UniqueInfos ann) m)
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
    :: (Ord ann,
        HasUnique n unique,
        MonadState (UniqueInfos ann) m,
        MonadWriter [UniqueError ann] m)
    => n -- ^ The variable
    -> ann -- ^ The annotation of the variable
    -> ScopeType -- ^ The scope type
    -> m ()
addDef n newDef tpe = do
    let def = ScopedLoc tpe newDef

    d@(_, uses) <- lookupDef n
    checkUndefined n def d
    modify $ insertByNameIndex n (Just def, uses)

-- | Check that a variable is currently undefined.
checkUndefined
    :: (HasUnique n u,
        MonadState (UniqueInfos ann) m,
        MonadWriter [UniqueError ann] m)
    => n -- ^ The variable
    -> ScopedLoc ann -- ^ The new definition
    -> UniqueInfo ann -- ^ The existing info
    -> m ()
checkUndefined n (ScopedLoc _ newDef) info = case info of
    (Just (ScopedLoc _ prevDef), _) -> tell [MultiplyDefined (n ^. theUnique) prevDef newDef]
    _                               -> pure ()

addUsage
    :: (Ord ann,
        HasUnique n unique,
        MonadState (UniqueInfos ann) m,
        MonadWriter [UniqueError ann] m)
    => n -- ^ The variable
    -> ann -- ^ The annotation of the variable
    -> ScopeType -- ^ The scope type
    -> m ()
addUsage n newUse tpe = do
    let use = ScopedLoc tpe newUse

    d@(def, uses) <- lookupDef n
    checkCoherency n use d
    checkDefined n use d
    modify $ insertByNameIndex n (def, Set.insert use uses)

checkDefined
    :: (HasUnique n u,
        MonadWriter [UniqueError ann] m)
    => n -- ^ The variable
    -> ScopedLoc ann -- ^ The new definition
    -> UniqueInfo ann -- ^ The existing info
    -> m ()
checkDefined n (ScopedLoc _ loc) (def, _) = case def of
    Nothing -> tell [FreeVariable (n ^. theUnique) loc]
    Just _  -> pure ()

checkCoherency
    :: (HasUnique n u,
        MonadWriter [UniqueError ann] m)
    => n -- ^ The variable
    -> ScopedLoc ann -- ^ The new definition
    -> UniqueInfo ann -- ^ The existing info
    -> m ()
checkCoherency n (ScopedLoc tpe loc) (def, uses) = do
    for_ def checkLoc
    for_ (Set.toList uses) checkLoc

    where
        checkLoc (ScopedLoc tpe' loc') = when (tpe' /= tpe) $
            tell [IncoherentUsage (n ^. theUnique) loc' loc]

-- | Given a PLC term, add all of its term and type definitions and usages, including its subterms
-- and subtypes, to a global map.
termDefs
    :: (Ord ann,
        HasUnique name TermUnique,
        HasUnique tyname TypeUnique,
        MonadState (UniqueInfos ann) m,
        MonadWriter [UniqueError ann] m)
    => Term tyname name uni fun ann
    -> m (Term tyname name uni fun ann)
termDefs tm = case tm of
    Var ann n         -> do
        addUsage n ann TermScope
        pure tm
    LamAbs ann n ty t -> do
        addDef n ann TermScope
        void $ typeDefs ty
        termDefs t
    IWrap _ pat arg t -> do
        void $ typeDefs pat
        void $ typeDefs arg
        termDefs t
    TyAbs ann tn _ t  -> do
        addDef tn ann TypeScope
        void $ termDefs t
        forMOf termSubtypes tm typeDefs
    TyInst _ t ty     -> do
        void $ typeDefs ty
        termDefs t
    _                  -> do
        void $ forMOf termSubterms tm termDefs
        forMOf termSubtypes tm typeDefs

-- | Given a type, add its type definition/usage, including its subtypes, to a global map.
typeDefs
    :: (Ord ann,
        HasUnique tyname TypeUnique,
        MonadState (UniqueInfos ann) m,
        MonadWriter [UniqueError ann] m)
    => Type tyname uni ann
    -> m (Type tyname uni ann)
typeDefs ty = case ty of
    TyVar ann n         -> do
        addUsage n ann TypeScope
        pure ty
    TyForall ann tn _ _t -> do
        addDef tn ann TypeScope
        forMOf typeSubtypes ty typeDefs
    TyLam ann tn _ _t    -> do
        addDef tn ann TypeScope
        forMOf typeSubtypes ty typeDefs
    _                    ->  forMOf typeSubtypes ty typeDefs

runTermDefs
    :: (Ord ann,
        HasUnique name TermUnique,
        HasUnique tyname TypeUnique,
        Monad m)
    => Term tyname name uni fun ann
    -> m (UniqueInfos ann, [UniqueError ann])
runTermDefs = runWriterT . flip execStateT mempty . termDefs

runTypeDefs
    :: (Ord ann,
        HasUnique tyname TypeUnique,
        Monad m)
    => Type tyname uni ann
    -> m (UniqueInfos ann, [UniqueError ann])
runTypeDefs = runWriterT . flip execStateT mempty . typeDefs
