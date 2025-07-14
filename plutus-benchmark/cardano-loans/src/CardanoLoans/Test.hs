{-# LANGUAGE BlockArguments        #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns        #-}
{-# LANGUAGE NoImplicitPrelude     #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE Strict                #-}

module CardanoLoans.Test where

import PlutusTx
import PlutusTx.Prelude

import CardanoLoans.Validator (LoanDatum (..), LoanRedeemer (..), validatorCode)
import PlutusLedgerApi.Data.V3
import PlutusLedgerApi.V1.Data.Value (assetClass)
import PlutusTx.Data.AssocMap qualified as Map
import PlutusTx.Data.List qualified as List

validatorCodeFullyApplied :: CompiledCode BuiltinUnit
validatorCodeFullyApplied =
  validatorCode `unsafeApplyCode` liftCodeDef (toBuiltinData testScriptContext)

testScriptContext :: ScriptContext
testScriptContext =
  ScriptContext
    { scriptContextTxInfo = txInfo
    , scriptContextRedeemer
    , scriptContextScriptInfo
    }
 where
  txInfo =
    TxInfo
      { txInfoInputs = mempty
      , txInfoReferenceInputs = mempty
      , txInfoOutputs = mempty
      , txInfoTxCerts = mempty
      , txInfoRedeemers = Map.empty
      , txInfoVotes = Map.empty
      , txInfoProposalProcedures = mempty
      , txInfoCurrentTreasuryAmount = Nothing
      , txInfoTreasuryDonation = Nothing
      , txInfoFee = 0
      , txInfoMint = emptyMintValue
      , txInfoWdrl = Map.empty
      , txInfoValidRange =
          Interval
            (LowerBound (Finite 110) True)
            (UpperBound (Finite 1100) True)
      , txInfoSignatories = List.singleton testBeneficiaryPKH
      , txInfoData = Map.empty
      , txInfoId = "058fdca70be67c74151cea3846be7f73342d92c0090b62c1052e6790ad83f145"
      }

  scriptContextRedeemer :: Redeemer
  scriptContextRedeemer = Redeemer $ toBuiltinData CloseAsk

  scriptContextScriptInfo :: ScriptInfo
  scriptContextScriptInfo =
    SpendingScript (TxOutRef txOutRefId txOutRefIdx) (Just datum)
    where
      txOutRefId = "058fdca70be67c74151cea3846be7f73342d92c0090b62c1052e6790ad83f145"
      txOutRefIdx = 0

      datum :: Datum
      datum = Datum (toBuiltinData testLoanDatum)

testLoanDatum :: LoanDatum
testLoanDatum =
  AskDatum
    { collateral = []
    -- , askBeacon = (CurrencySymbol,TokenName)
    -- , borrowerId = (CurrencySymbol,TokenName)
    -- , loanAsset = (CurrencySymbol,TokenName)
    -- , loanPrinciple = Integer
    -- , loanTerm = POSIXTime
    }

testBeneficiaryPKH :: PubKeyHash
testBeneficiaryPKH = PubKeyHash ""
