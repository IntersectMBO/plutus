module PlutusLedgerApi.MachineParameters where

import PlutusLedgerApi.Common

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
    (defaultCaserBuiltinFor majorPV)
    (mkMachineVariantParameters builtinSemVar $ cekCostModelForVariant builtinSemVar)
  where
    -- See Note [Mapping of protocol versions and ledger languages to semantics variants].
    builtinSemVar
      | majorPV < vanRossemPV = case ledgerLang of
          PlutusV1 -> conwayDependentVariant
          PlutusV2 -> conwayDependentVariant
          PlutusV3 -> DefaultFunSemanticsVariantC
          -- 'PlutusV4' doesn't exist before the Dijkstra HF, which comes after
          -- van Rossem, so this case is vacuous.
          PlutusV4 -> DefaultFunSemanticsVariantE
      | majorPV < dijkstraPV = case ledgerLang of
          PlutusV1 -> DefaultFunSemanticsVariantD
          PlutusV2 -> DefaultFunSemanticsVariantD
          PlutusV3 -> DefaultFunSemanticsVariantE
          PlutusV4 -> DefaultFunSemanticsVariantE
      | otherwise = case ledgerLang of
          PlutusV1 -> DefaultFunSemanticsVariantF
          PlutusV2 -> DefaultFunSemanticsVariantF
          PlutusV3 -> DefaultFunSemanticsVariantG
          PlutusV4 -> DefaultFunSemanticsVariantG
    conwayDependentVariant =
      if majorPV < changPV
        then DefaultFunSemanticsVariantA
        else DefaultFunSemanticsVariantB
