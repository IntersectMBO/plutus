module PlutusLedgerApi.MachineParameters where

import PlutusLedgerApi.Common
import PlutusLedgerApi.Common.ProtocolVersions (futurePV)

import PlutusCore.Builtin (CaserBuiltin (..), caseBuiltin, unavailableCaserBuiltin)
import PlutusCore.Default (BuiltinSemanticsVariant (..))
import PlutusCore.Evaluation.Machine.ExBudgetingDefaults (cekCostModelForVariant)
import PlutusCore.Evaluation.Machine.MachineParameters (MachineParameters (..),
                                                        mkMachineVariantParameters)
import PlutusCore.Evaluation.Machine.MachineParameters.Default (DefaultMachineParameters)

machineParametersFor
  :: PlutusLedgerLanguage
  -> MajorProtocolVersion
  -> DefaultMachineParameters
machineParametersFor ledgerLang majorPV =
  MachineParameters
      (if majorPV < futurePV
        then unavailableCaserBuiltin $ getMajorProtocolVersion majorPV
        else CaserBuiltin caseBuiltin)
      (mkMachineVariantParameters builtinSemVar $ cekCostModelForVariant builtinSemVar)
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
