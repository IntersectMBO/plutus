module PlutusLedgerApi.MachineParameters where

import PlutusCore.Default (BuiltinSemanticsVariant (..))
import PlutusCore.Evaluation.Machine.ExBudgetingDefaults (cekCostModelForVariant)
import PlutusCore.Evaluation.Machine.MachineParameters (mkMachineParameters)
import PlutusCore.Evaluation.Machine.MachineParameters.Default (DefaultMachineParameters)
import PlutusLedgerApi.Common

machineParametersFor
  :: PlutusLedgerLanguage
  -> MajorProtocolVersion
  -> DefaultMachineParameters
machineParametersFor ledgerLang majorPV =
  mkMachineParameters builtinSemVar (cekCostModelForVariant builtinSemVar)
 where
  builtinSemVar =
    case ledgerLang of
      PlutusV1 -> conwayDependentVariant
      PlutusV2 -> conwayDependentVariant
      PlutusV3 -> DefaultFunSemanticsVariantC
  conwayDependentVariant =
    if majorPV < changPV
      then DefaultFunSemanticsVariantA
      else DefaultFunSemanticsVariantB
