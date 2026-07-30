-- editorconfig-checker-disable-file
{-# LANGUAGE FlexibleContexts #-}

-- | Functions for computing variable usage inside terms.
module UntypedPlutusCore.Analysis.Usages (termUsages, Usages, getUsageCount, allUsed) where

import UntypedPlutusCore.Core.Type
import UntypedPlutusCore.Subst

import PlutusCore qualified as PLC
import PlutusCore.Name.Unique qualified as PLC

import Control.Lens

import Data.MultiSet qualified as MSet
import Data.MultiSet.Lens
import Data.Set qualified as Set

type Usages = MSet.MultiSet PLC.Unique

-- | Get the usage count of @n@.
getUsageCount :: PLC.HasUnique n unique => n -> Usages -> Int
getUsageCount n = MSet.occur (n ^. PLC.unique . coerced)

-- | Get a set of @n@s which are used at least once.
allUsed :: Usages -> Set.Set PLC.Unique
allUsed = MSet.toSet

termUsages
  :: PLC.HasUnique name PLC.TermUnique
  => Term name uni fun a
  -> Usages
termUsages = multiSetOf (vTerm . PLC.theUnique)
