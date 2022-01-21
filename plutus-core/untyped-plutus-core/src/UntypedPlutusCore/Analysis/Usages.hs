{-# LANGUAGE FlexibleContexts #-}
-- | Functions for computing variable usage inside terms.
module UntypedPlutusCore.Analysis.Usages (runTermUsages, Usages, getUsageCount, allUsed) where

import UntypedPlutusCore.Core.Plated
import UntypedPlutusCore.Core.Type

import PlutusCore qualified as PLC
import PlutusCore.Name qualified as PLC

import Control.Lens
import Control.Monad.State

import Data.Coerce
import Data.Foldable
import Data.Map qualified as Map
import Data.Set qualified as Set

-- | Variable uses, as a map from the 'PLC.Unique' to its usage count. Unused variables may be missing
-- or have usage count 0.
type Usages = Map.Map PLC.Unique Int

addUsage :: (PLC.HasUnique n unique) => n -> Usages -> Usages
addUsage n usages =
    let
        u = coerce $ n ^. PLC.unique
        old = Map.findWithDefault 0 u usages
    in Map.insert u (old+1) usages

-- | Get the usage count of @n@.
getUsageCount :: (PLC.HasUnique n unique) => n -> Usages -> Int
getUsageCount n usages = Map.findWithDefault 0 (n ^. PLC.unique . coerced) usages

-- | Get a set of @n@s which are used at least once.
allUsed :: Usages -> Set.Set PLC.Unique
allUsed usages = Map.keysSet $ Map.filter (> 0) usages

-- | Compute the 'Usages' for a 'Term'.
runTermUsages
    :: (PLC.HasUnique name PLC.TermUnique)
    => Term name uni fun a
    -> Usages
runTermUsages term = execState (termUsages term) mempty

termUsages
    :: (MonadState Usages m, PLC.HasUnique name PLC.TermUnique)
    => Term name uni fun a
    -> m ()
termUsages (Var _ n) = modify (addUsage n)
termUsages term      = traverse_ termUsages (term ^.. termSubterms)
