{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE Strict #-}
{-# LANGUAGE NoImplicitPrelude #-}

module LinearVesting.Test where

import PlutusTx
import PlutusTx.Prelude hiding ((<>))

import LinearVesting.Validator (VestingDatum (..), VestingRedeemer (..), validatorCode)
import PlutusLedgerApi.Data.V3 qualified as PV3D
import PlutusLedgerApi.Test.ScriptContextBuilder.Builder
  ( buildScriptContext
  , withAddress
  , withInlineDatum
  , withOutRef
  , withSigner
  , withSpendingScript
  , withValidRange
  )
import PlutusLedgerApi.V1.Data.Value (assetClass)
import PlutusLedgerApi.V3 qualified as PV3
import Prelude ((<>))

validatorCodeFullyApplied :: CompiledCode BuiltinUnit
validatorCodeFullyApplied =
  validatorCode `unsafeApplyCode` liftCodeDef (toBuiltinData testScriptContext)

testScriptContext :: PV3.ScriptContext
testScriptContext =
  buildScriptContext
    ( withValidRange
        ( PV3.Interval
            (PV3.LowerBound (PV3.Finite 110) True)
            (PV3.UpperBound (PV3.Finite 1100) True)
        )
        <> withSigner testBeneficiaryPKH
        <> withSpendingScript
          (toBuiltinData FullUnlock)
          ( withOutRef (PV3.TxOutRef txOutRefId txOutRefIdx)
              <> withAddress (PV3.Address (PV3.ScriptCredential scriptHash) Nothing)
              <> withInlineDatum (toBuiltinData testVestingDatum)
          )
    )
  where
    txOutRefId :: PV3.TxId
    txOutRefId = "058fdca70be67c74151cea3846be7f73342d92c0090b62c1052e6790ad83f145"
    txOutRefIdx :: Integer
    txOutRefIdx = 0
    scriptHash :: PV3.ScriptHash
    scriptHash = PV3.ScriptHash "deadbeef"

testVestingDatum :: VestingDatum
testVestingDatum =
  VestingDatum
    { beneficiary = PV3D.Address (PV3D.PubKeyCredential testBeneficiaryPKHData) Nothing
    , vestingAsset = assetClass (PV3D.CurrencySymbol "$") (PV3D.TokenName "test-asset")
    , totalVestingQty = 1000
    , vestingPeriodStart = 0
    , vestingPeriodEnd = 100
    , firstUnlockPossibleAfter = 10
    , totalInstallments = 10
    }

testBeneficiaryPKH :: PV3.PubKeyHash
testBeneficiaryPKH = PV3.PubKeyHash ""

testBeneficiaryPKHData :: PV3D.PubKeyHash
testBeneficiaryPKHData = PV3D.PubKeyHash ""
