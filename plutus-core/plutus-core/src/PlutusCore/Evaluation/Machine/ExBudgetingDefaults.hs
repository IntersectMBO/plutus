{-# LANGUAGE DataKinds       #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies    #-}

module PlutusCore.Evaluation.Machine.ExBudgetingDefaults
    ( defaultBuiltinsRuntime
    , defaultCekCostModel
    , defaultCekMachineCosts
    , defaultCekParameters
    , defaultCostModelParams
    , unitCekMachineCosts
    , unitCekParameters
    , defaultBuiltinCostModel
    )

where

import           Data.Aeson.THReader

import           PlutusCore.Constant

import qualified PlutusCore.DataFilePaths                                 as DFP
import           PlutusCore.Default
import           PlutusCore.Evaluation.Machine.BuiltinCostModel
import           PlutusCore.Evaluation.Machine.CostModelInterface
import           PlutusCore.Evaluation.Machine.ExBudget                   ()
import           PlutusCore.Evaluation.Machine.ExMemory                   ()
import           PlutusCore.Evaluation.Machine.MachineParameters

import           UntypedPlutusCore.Evaluation.Machine.Cek.CekMachineCosts
import           UntypedPlutusCore.Evaluation.Machine.Cek.Internal

-- | The default cost model for built-in functions.
defaultBuiltinCostModel :: BuiltinCostModel
defaultBuiltinCostModel =
  $$(readJSONFromFile DFP.builtinCostModelFile)

{- Note [Modifying the cost model]
   When the Haskell representation of the cost model is changed, for example by
   adding a new builtin or changing the name of an existing one,
   readJSONFromFile will fail when it tries to read a JSON file generated using
   the previous version.  When this happens, uncomment the three lines below (and
   comment out the three above) then rerun

      cabal run plutus-core:update-cost-model

   This will generate a new JSON file filled with default values.  After that,
   restore this file to its previous state and then run "update-cost-model"
   again to fill in the JSON file with the correct values (assuming that
   suitable benchmarking data is in benching.csv and that models.R contains R
   code to generate cost models for any new functions).

   Alternatively, modify builtinCostModelFile by hand so that it matches the new
   format.
 -}

-- import           Data.Default
-- defaultBuiltinCostModel :: BuiltinCostModel
-- defaultBuiltinCostModel = def

-- | Default costs for CEK machine instructions.
defaultCekMachineCosts :: CekMachineCosts
defaultCekMachineCosts =
  $$(readJSONFromFile DFP.cekMachineCostsFile)

defaultCekCostModel :: CostModel CekMachineCosts BuiltinCostModel
defaultCekCostModel = CostModel defaultCekMachineCosts defaultBuiltinCostModel
--- defaultCekMachineCosts is CekMachineCosts

-- | The default cost model data.  This is exposed to the ledger, so let's not
-- confuse anybody by mentioning the CEK machine
defaultCostModelParams :: Maybe CostModelParams
defaultCostModelParams = extractCostModelParams defaultCekCostModel

defaultCekParameters :: MachineParameters CekMachineCosts CekValue DefaultUni DefaultFun
defaultCekParameters = toMachineParameters defaultCekCostModel

unitCekParameters :: MachineParameters CekMachineCosts CekValue DefaultUni DefaultFun
unitCekParameters = toMachineParameters (CostModel unitCekMachineCosts defaultBuiltinCostModel)

defaultBuiltinsRuntime :: HasConstantIn DefaultUni term => BuiltinsRuntime DefaultFun term
defaultBuiltinsRuntime = toBuiltinsRuntime defaultBuiltinCostModel
