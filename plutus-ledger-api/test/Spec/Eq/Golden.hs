{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}

{-| Golden tests for deriveEq instances in plutus-ledger-api.
These tests capture the exact generated code for types where manual Eq instances
were replaced with deriveEq, providing confidence that derived instances match
the original manual implementations. -}
module Spec.Eq.Golden (eqGoldenTests) where

import PlutusTx.Eq (deriveEq)
import PlutusTx.Test.Golden (goldenCodeGen, goldenCodeGenNormalized)
import Test.Tasty (TestTree)
import Test.Tasty.Extras (runTestNested)

-- V1 types
import PlutusLedgerApi.V1.Address qualified as V1
import PlutusLedgerApi.V1.Contexts qualified as V1
import PlutusLedgerApi.V1.Credential qualified as V1
import PlutusLedgerApi.V1.DCert qualified as V1
import PlutusLedgerApi.V1.Interval qualified as V1

-- V1 Data types
import PlutusLedgerApi.V1.Data.Address qualified as V1D
import PlutusLedgerApi.V1.Data.Contexts qualified as V1D
import PlutusLedgerApi.V1.Data.Credential qualified as V1D
import PlutusLedgerApi.V1.Data.DCert qualified as V1D

-- V2 types
import PlutusLedgerApi.V2.Contexts qualified as V2
import PlutusLedgerApi.V2.Tx qualified as V2

-- V2 Data types
import PlutusLedgerApi.V2.Data.Contexts qualified as V2D
import PlutusLedgerApi.V2.Data.Tx qualified as V2D

-- V3 types
import PlutusLedgerApi.V3.Contexts qualified as V3
import PlutusLedgerApi.V3.Tx qualified as V3

-- V3 Data types
import PlutusLedgerApi.V3.Data.Contexts qualified as V3D
import PlutusLedgerApi.V3.Data.Tx qualified as V3D

eqGoldenTests :: TestTree
eqGoldenTests =
  runTestNested
    ["test", "Spec", "Eq", "Golden"]
    [ -- V1 types
      $(goldenCodeGen "V1.Address" (deriveEq ''V1.Address))
    , $(goldenCodeGen "V1.TxInInfo" (deriveEq ''V1.TxInInfo))
    , $(goldenCodeGen "V1.ScriptPurpose" (deriveEq ''V1.ScriptPurpose))
    , $(goldenCodeGen "V1.TxInfo" (deriveEq ''V1.TxInfo))
    , $(goldenCodeGen "V1.ScriptContext" (deriveEq ''V1.ScriptContext))
    , $(goldenCodeGen "V1.Credential" (deriveEq ''V1.Credential))
    , $(goldenCodeGen "V1.StakingCredential" (deriveEq ''V1.StakingCredential))
    , $(goldenCodeGen "V1.DCert" (deriveEq ''V1.DCert))
    , $(goldenCodeGen "V1.Extended" (deriveEq ''V1.Extended))
    , $(goldenCodeGen "V1.TxOutRef" (deriveEq ''V1.TxOutRef))
    , $(goldenCodeGen "V1.TxOut" (deriveEq ''V1.TxOut))
    , -- V1 Data types
      -- See Note [Stripping TH-generated unique suffixes in golden tests]
      -- in PlutusTx.Test.Golden
      $(goldenCodeGenNormalized "V1D.Address" (deriveEq ''V1D.Address))
    , $(goldenCodeGenNormalized "V1D.TxInInfo" (deriveEq ''V1D.TxInInfo))
    , $(goldenCodeGenNormalized "V1D.ScriptPurpose" (deriveEq ''V1D.ScriptPurpose))
    , $(goldenCodeGenNormalized "V1D.TxInfo" (deriveEq ''V1D.TxInfo))
    , $(goldenCodeGenNormalized "V1D.ScriptContext" (deriveEq ''V1D.ScriptContext))
    , $(goldenCodeGenNormalized "V1D.Credential" (deriveEq ''V1D.Credential))
    , $(goldenCodeGenNormalized "V1D.StakingCredential" (deriveEq ''V1D.StakingCredential))
    , $(goldenCodeGenNormalized "V1D.DCert" (deriveEq ''V1D.DCert))
    , $(goldenCodeGenNormalized "V1D.TxOutRef" (deriveEq ''V1D.TxOutRef))
    , $(goldenCodeGenNormalized "V1D.TxOut" (deriveEq ''V1D.TxOut))
    , -- V2 Original types
      $(goldenCodeGen "V2.TxInInfo" (deriveEq ''V2.TxInInfo))
    , $(goldenCodeGen "V2.OutputDatum" (deriveEq ''V2.OutputDatum))
    , $(goldenCodeGen "V2.TxOut" (deriveEq ''V2.TxOut))
    , -- V2 Data types
      $(goldenCodeGenNormalized "V2D.TxInInfo" (deriveEq ''V2D.TxInInfo))
    , $(goldenCodeGenNormalized "V2D.OutputDatum" (deriveEq ''V2D.OutputDatum))
    , $(goldenCodeGenNormalized "V2D.TxOut" (deriveEq ''V2D.TxOut))
    , -- V3 Original types
      $(goldenCodeGen "V3.DRep" (deriveEq ''V3.DRep))
    , $(goldenCodeGen "V3.Delegatee" (deriveEq ''V3.Delegatee))
    , $(goldenCodeGen "V3.TxCert" (deriveEq ''V3.TxCert))
    , $(goldenCodeGen "V3.Voter" (deriveEq ''V3.Voter))
    , $(goldenCodeGen "V3.Vote" (deriveEq ''V3.Vote))
    , $(goldenCodeGen "V3.GovernanceActionId" (deriveEq ''V3.GovernanceActionId))
    , $(goldenCodeGen "V3.Constitution" (deriveEq ''V3.Constitution))
    , $(goldenCodeGen "V3.ProtocolVersion" (deriveEq ''V3.ProtocolVersion))
    , $(goldenCodeGen "V3.TxInInfo" (deriveEq ''V3.TxInInfo))
    , $(goldenCodeGen "V3.TxOutRef" (deriveEq ''V3.TxOutRef))
    , -- V3 Data types
      $(goldenCodeGenNormalized "V3D.DRep" (deriveEq ''V3D.DRep))
    , $(goldenCodeGenNormalized "V3D.Delegatee" (deriveEq ''V3D.Delegatee))
    , $(goldenCodeGenNormalized "V3D.TxCert" (deriveEq ''V3D.TxCert))
    , $(goldenCodeGenNormalized "V3D.Voter" (deriveEq ''V3D.Voter))
    , $(goldenCodeGenNormalized "V3D.Vote" (deriveEq ''V3D.Vote))
    , $(goldenCodeGenNormalized "V3D.GovernanceActionId" (deriveEq ''V3D.GovernanceActionId))
    , $(goldenCodeGenNormalized "V3D.Constitution" (deriveEq ''V3D.Constitution))
    , $(goldenCodeGenNormalized "V3D.ProtocolVersion" (deriveEq ''V3D.ProtocolVersion))
    , $(goldenCodeGenNormalized "V3D.TxInInfo" (deriveEq ''V3D.TxInInfo))
    , $(goldenCodeGenNormalized "V3D.TxOutRef" (deriveEq ''V3D.TxOutRef))
    ]
