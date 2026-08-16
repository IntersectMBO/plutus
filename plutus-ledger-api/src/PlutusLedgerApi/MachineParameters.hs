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
    ( if majorPV < vanRossemPV
        then unavailableCaserBuiltin $ getMajorProtocolVersion majorPV
        else CaserBuiltin caseBuiltin
    )
    (mkMachineVariantParameters builtinSemVar $ cekCostModelForVariant builtinSemVar)
  where
    -- See Note [Mapping of protocol versions and ledger languages to semantics variants].
    builtinSemVar =
      if majorPV < vanRossemPV
        then case ledgerLang of
          PlutusV1 -> conwayDependentVariant
          PlutusV2 -> conwayDependentVariant
          PlutusV3 -> DefaultFunSemanticsVariantC
          -- 'PlutusV4' doesn't exist before the Dijkstra HF, which comes after
          -- van Rossem, so this case is vacuous.
          PlutusV4 -> DefaultFunSemanticsVariantE
        else case ledgerLang of
          PlutusV1 -> DefaultFunSemanticsVariantD
          PlutusV2 -> DefaultFunSemanticsVariantD
          PlutusV3 -> DefaultFunSemanticsVariantE
          PlutusV4 -> DefaultFunSemanticsVariantE
    conwayDependentVariant =
      if majorPV < changPV
        then DefaultFunSemanticsVariantA
        else DefaultFunSemanticsVariantB
