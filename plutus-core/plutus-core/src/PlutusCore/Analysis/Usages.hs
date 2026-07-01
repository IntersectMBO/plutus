{-# LANGUAGE FlexibleContexts #-}

-- | Functions for computing variable usage inside types.
module PlutusCore.Analysis.Usages (typeUsages, Usages, getUsageCount, allUsed) where

import PlutusCore.Core
import PlutusCore.Name.Unique qualified as PLC
import PlutusCore.Subst (tvTy)

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

typeUsages
  :: PLC.HasUnique tyname PLC.TypeUnique
  => Type tyname uni a
  -> Usages
typeUsages = multiSetOf (tvTy . PLC.theUnique)
