module PlutusLedgerApi.MachineParameters where

import PlutusLedgerApi.Common

import PlutusCore.Builtin (CaserBuiltin (..), caseBuiltin, unavailableCaserBuiltin)
import PlutusCore.Default (BuiltinSemanticsVariant (..))
import PlutusCore.Evaluation.Machine.ExBudgetingDefaults (cekCostModelForVariant)
import PlutusCore.Evaluation.Machine.MachineParameters
  ( MachineParameters (..)
  , mkMachineVariantParameters
  )
import PlutusCore.Evaluation.Machine.MachineParameters.Default (DefaultMachineParameters)

machineParametersFor
  :: PlutusLedgerLanguage
  -> MajorProtocolVersion
  -> DefaultMachineParameters
machineParametersFor ledgerLang majorPV =
  MachineParameters
    ( if majorPV < pv11PV
        then unavailableCaserBuiltin $ getMajorProtocolVersion majorPV
        else CaserBuiltin caseBuiltin
    )
    (mkMachineVariantParameters builtinSemVar $ cekCostModelForVariant builtinSemVar)
  where
    builtinSemVar =
      if majorPV < pv11PV
        then case ledgerLang of
          PlutusV1 -> conwayDependentVariant
          PlutusV2 -> conwayDependentVariant
          PlutusV3 -> DefaultFunSemanticsVariantC
        else case ledgerLang of
          PlutusV1 -> DefaultFunSemanticsVariantD
          PlutusV2 -> DefaultFunSemanticsVariantD
          PlutusV3 -> DefaultFunSemanticsVariantE
    conwayDependentVariant =
      if majorPV < changPV
        then DefaultFunSemanticsVariantA
        else DefaultFunSemanticsVariantB
