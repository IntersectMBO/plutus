{-# LANGUAGE LambdaCase #-}
-- | Definition analysis for Plutus Core.
module Language.PlutusCore.Analysis.Definitions where

import           Language.PlutusCore.Error
import           Language.PlutusCore.Name
import           Language.PlutusCore.Type

import           Data.Functor.Foldable

import           Control.Lens              hiding (use, uses)
import           Control.Monad.Except
import           Control.Monad.State
import           Control.Monad.Writer

import           Data.Foldable
import qualified Data.Set                  as Set

{- Note [Unique usage errors]
The definitions analysis can find a number of problems with usage of uniques, however
clients may not always want to throw an error on all of them, hence we simply return
them all and allow the client to chose if they want to throw some of them.
-}

-- | Information about a unique, a pair of a definition if we have one and a set of uses.
type UniqueInfo a = (Maybe (ScopedLoc a), Set.Set (ScopedLoc a))
type UniqueInfos a = UniqueMap Unique (UniqueInfo a)

data ScopedLoc a = ScopedLoc ScopeType a deriving (Eq, Ord)

-- | Tag for distinguishing between whether we are talking about the term scope
-- for variables or the type scope for variables.
data ScopeType = TermScope | TypeScope deriving (Eq, Ord)

lookupDef
    :: (Ord a,
        HasUnique name unique,
        MonadState (UniqueInfos a) m)
    => name
    -> m (UniqueInfo a)
lookupDef n = do
    previousDef <- gets $ lookupNameIndex n
    case previousDef of
        Just d -> pure d
        Nothing -> do
            let empty = (Nothing, mempty)
            modify $ insertByNameIndex n empty
            pure empty

addDef
    :: (Ord a,
        HasUnique n unique,
        MonadState (UniqueInfos a) m,
        MonadWriter [UniqueError a] m)
    => n -- ^ The variable
    -> a -- ^ The annotation of the variable
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
        MonadState (UniqueInfos a) m,
        MonadWriter [UniqueError a] m)
    => n -- ^ The variable
    -> ScopedLoc a -- ^ The new definition
    -> UniqueInfo a -- ^ The existing info
    -> m ()
checkUndefined n (ScopedLoc _ newDef) info = case info of
    (Just (ScopedLoc _ prevDef), _) -> tell [MultiplyDefined (n ^. unique . coerced) prevDef newDef]
    _                               -> pure ()

addUsage
    :: (Ord a,
        HasUnique n unique,
        MonadState (UniqueInfos a) m,
        MonadWriter [UniqueError a] m)
    => n -- ^ The variable
    -> a -- ^ The annotation of the variable
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
        MonadWriter [UniqueError a] m)
    => n -- ^ The variable
    -> ScopedLoc a -- ^ The new definition
    -> UniqueInfo a -- ^ The existing info
    -> m ()
checkDefined n (ScopedLoc _ loc) (def, _) = case def of
    Nothing -> tell [FreeVariable (n ^. unique . coerced) loc]
    Just _  -> pure ()

checkCoherency
    :: (HasUnique n u,
        MonadWriter [UniqueError a] m)
    => n -- ^ The variable
    -> ScopedLoc a -- ^ The new definition
    -> UniqueInfo a -- ^ The existing info
    -> m ()
checkCoherency n (ScopedLoc tpe loc) (def, uses) = do
    for_ def checkLoc
    for_ (Set.toList uses) checkLoc

    where
        checkLoc (ScopedLoc tpe' loc') = when (tpe' /= tpe) $
            tell [IncoherentUsage (n ^. unique . coerced) loc' loc]

termDefs
    :: (Ord a,
        HasUnique (name a) TermUnique,
        HasUnique (tyname a) TypeUnique,
        MonadState (UniqueInfos a) m,
        MonadWriter [UniqueError a] m)
    => Term tyname name a
    -> m ()
termDefs = cata $ \case
    VarF a n           -> addUsage n a TermScope
    LamAbsF a n ty t   -> addDef n a TermScope >> typeDefs ty >> t
    IWrapF _ pat arg t -> typeDefs pat >> typeDefs arg >> t
    TyAbsF a tn _ t    -> addDef tn a TypeScope >> t
    TyInstF _ t ty     -> t >> typeDefs ty
    x                  -> sequence_ x

typeDefs
    :: (Ord a,
        HasUnique (tyname a) TypeUnique,
        MonadState (UniqueInfos a) m,
        MonadWriter [UniqueError a] m)
    => Type tyname a
    -> m ()
typeDefs = cata $ \case
    TyVarF a n         -> addUsage n a TypeScope
    TyForallF a tn _ t -> addDef tn a TypeScope >> t
    TyLamF a tn _ t    -> addDef tn a TypeScope >> t
    x                  -> sequence_ x

runTermDefs
    :: (Ord a,
        HasUnique (name a) TermUnique,
        HasUnique (tyname a) TypeUnique,
        Monad m)
    => Term tyname name a
    -> m (UniqueInfos a, [UniqueError a])
runTermDefs = runWriterT . flip execStateT mempty . termDefs

runTypeDefs
    :: (Ord a,
        HasUnique (tyname a) TypeUnique,
        Monad m)
    => Type tyname a
    -> m (UniqueInfos a, [UniqueError a])
runTypeDefs = runWriterT . flip execStateT mempty . typeDefs
