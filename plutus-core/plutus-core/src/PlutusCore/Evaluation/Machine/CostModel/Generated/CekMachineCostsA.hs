-- This file contains the CEK machine costs for variant A.
-- It corresponds to the previous cekMachineCostsA.json file.
{-# LANGUAGE RecordWildCards #-}

module PlutusCore.Evaluation.Machine.CostModel.Generated.CekMachineCostsA (cekMachineCostsA) where

import Data.Functor.Identity
import PlutusCore.Evaluation.Machine.ExMemory
import UntypedPlutusCore.Evaluation.Machine.Cek.CekMachineCosts

cekMachineCostsA :: CekMachineCosts
cekMachineCostsA =
  CekMachineCostsBase
    { cekStartupCost = Identity (ExBudget 100 100)
    , cekVarCost = Identity (ExBudget 23000 100)
    , cekConstCost = Identity (ExBudget 23000 100)
    , cekLamCost = Identity (ExBudget 23000 100)
    , cekDelayCost = Identity (ExBudget 23000 100)
    , cekForceCost = Identity (ExBudget 23000 100)
    , cekApplyCost = Identity (ExBudget 23000 100)
    , cekBuiltinCost = Identity (ExBudget 23000 100)
    , cekConstrCost = Identity (ExBudget 23000 100)
    , cekCaseCost = Identity (ExBudget 23000 100)
    }
