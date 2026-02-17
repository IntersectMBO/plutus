-- This file contains the CEK machine costs for variant C.
-- It corresponds to the previous cekMachineCostsC.json file.
{-# LANGUAGE RecordWildCards #-}

module PlutusCore.Evaluation.Machine.CostModel.Generated.CekMachineCostsC (cekMachineCostsC) where

import Data.Functor.Identity
import PlutusCore.Evaluation.Machine.ExMemory
import UntypedPlutusCore.Evaluation.Machine.Cek.CekMachineCosts

cekMachineCostsC :: CekMachineCosts
cekMachineCostsC =
  CekMachineCostsBase
    { cekStartupCost = Identity (ExBudget 100 100)
    , cekVarCost = Identity (ExBudget 16000 100)
    , cekConstCost = Identity (ExBudget 16000 100)
    , cekLamCost = Identity (ExBudget 16000 100)
    , cekDelayCost = Identity (ExBudget 16000 100)
    , cekForceCost = Identity (ExBudget 16000 100)
    , cekApplyCost = Identity (ExBudget 16000 100)
    , cekBuiltinCost = Identity (ExBudget 16000 100)
    , cekConstrCost = Identity (ExBudget 16000 100)
    , cekCaseCost = Identity (ExBudget 16000 100)
    }
