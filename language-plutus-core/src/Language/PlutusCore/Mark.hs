{-# LANGUAGE LambdaCase #-}

module Language.PlutusCore.Mark
    ( markNonFresh
    , markNonFreshBelow
    , markNonFreshTerm
    , markNonFreshType
    , markNonFreshProgram
    ) where

import           Language.PlutusCore.Name
import           Language.PlutusCore.Quote
import           Language.PlutusCore.Type

import           Control.Lens
import           Control.Monad.State
import           Data.Functor.Foldable
import           Data.Maybe                (fromMaybe)
import qualified Data.Set                  as Set

-- | Marks all the 'Unique's in a type as used, so they will not be generated in future. Useful if you
-- have a type which was not generated in 'Quote'.
markNonFreshType
    :: (HasUnique (tyname ann) TypeUnique, MonadQuote m)
    => Type tyname ann
    -> m ()
markNonFreshType = markNonFreshMax . collectTypeUniques

-- | Marks all the 'Unique's in a term as used, so they will not be generated in future. Useful if you
-- have a term which was not generated in 'Quote'.
markNonFreshTerm
    :: (HasUnique (tyname ann) TypeUnique, HasUnique (name ann) TermUnique, MonadQuote m)
    => Term tyname name ann
    -> m ()
markNonFreshTerm = markNonFreshMax . collectTermUniques

-- | Marks all the 'Unique's in a program as used, so they will not be generated in future. Useful if you
-- have a program which was not generated in 'Quote'.
markNonFreshProgram
    :: (HasUnique (tyname ann) TypeUnique, HasUnique (name ann) TermUnique, MonadQuote m)
    => Program tyname name ann
    -> m ()
markNonFreshProgram (Program _ _ body) = markNonFreshTerm body

-- | Mark the maximal 'Unique' from a set of 'Unique's (and implicitly all 'Unique's less than it)
-- as used, so they will not be generated in future.
markNonFreshMax :: MonadQuote m => Set.Set Unique -> m ()
markNonFreshMax = markNonFresh . fromMaybe (Unique 0) . Set.lookupMax

-- | Mark a given 'Unique' (and implicitly all 'Unique's less than it) as used, so they will not be generated in future.
markNonFresh :: MonadQuote m => Unique -> m ()
markNonFresh nonFresh = liftQuote $ do
    nextU <- QuoteT get
    QuoteT $ put $ Unique (max (unUnique nonFresh + 1) (unUnique nextU))

-- | Mark a all 'Unique's less than the given 'Unique' as used, so they will not be generated in future.
markNonFreshBelow :: MonadQuote m => Unique -> m ()
markNonFreshBelow nonFresh = liftQuote $ do
    nextU <- QuoteT get
    QuoteT $ put $ Unique (max (unUnique nonFresh) (unUnique nextU))

collectTypeUniques :: (HasUnique (tyname ann) TypeUnique) => Type tyname ann -> Set.Set Unique
collectTypeUniques = cata f where
    f = \case
        TyVarF _ tn        -> Set.singleton (tn ^. unique . coerced)
        TyForallF _ tn _ t -> Set.insert (tn ^. unique . coerced) t
        TyLamF _ tn _ t    -> Set.insert (tn ^. unique . coerced) t
        TyAppF _ t1 t2     -> t1 <> t2
        TyFunF _ t1 t2     -> t1 <> t2
        TyIFixF _ pat arg  -> pat <> arg
        _                  -> mempty

collectTermUniques
    :: (HasUnique (tyname ann) TypeUnique, HasUnique (name ann) TermUnique)
    => Term tyname name ann -> Set.Set Unique
collectTermUniques = cata f where
    f = \case
        VarF _ n           -> Set.singleton (n ^. unique . coerced)
        LamAbsF _ n ty t   -> Set.insert (n ^. unique . coerced) (collectTypeUniques ty <> t)
        TyAbsF _ tn _ t    -> Set.insert (tn ^. unique . coerced) t
        TyInstF _ t ty     -> t <> collectTypeUniques ty
        ApplyF _ t1 t2     -> t1 <> t2
        IWrapF _ pat arg t -> collectTypeUniques pat <> collectTypeUniques arg <> t
        UnwrapF _ t        -> t
        ErrorF _ ty        -> collectTypeUniques ty
        _                  -> mempty
