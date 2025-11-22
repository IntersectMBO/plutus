{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE Strict #-}
{-# LANGUAGE NoImplicitPrelude #-}

module CardanoLoans.Test where

import PlutusTx
import PlutusTx.Prelude

import CardanoLoans.Validator (LoanDatum (..), LoanRedeemer (..), loanValidatorCode)
import PlutusLedgerApi.V1.Address (pubKeyHashAddress)
import PlutusLedgerApi.V1.Value qualified as Value
import PlutusLedgerApi.V2.Tx qualified as Tx
import PlutusLedgerApi.V3
import PlutusTx.AssocMap qualified as Map

validatorCodeFullyApplied :: CompiledCode BuiltinUnit
validatorCodeFullyApplied =
  loanValidatorCode `unsafeApplyCode` liftCodeDef (toBuiltinData testScriptContext)

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
        { txInfoInputs =
            [ TxInInfo
                { txInInfoOutRef = txOutRef
                , txInInfoResolved = Tx.pubKeyHashTxOut (Value.lovelaceValue 1000) testBeneficiaryPKH
                }
            ]
        , txInfoReferenceInputs = mempty
        , txInfoOutputs =
            [ TxOut
                { txOutAddress = pubKeyHashAddress testBeneficiaryPKH
                , txOutValue = Value.lovelaceValue 1000
                , txOutDatum = NoOutputDatum
                , txOutReferenceScript = Nothing
                }
            ]
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
        , txInfoSignatories = [testBeneficiaryPKH]
        , txInfoData = Map.empty
        , txInfoId = "058fdca70be67c74151cea3846be7f73342d92c0090b62c1052e6790ad83f145"
        }

    scriptContextRedeemer :: Redeemer
    scriptContextRedeemer = Redeemer $ toBuiltinData CloseAsk

    txOutRef :: TxOutRef
    txOutRef = TxOutRef txOutRefId txOutRefIdx
      where
        txOutRefId = "058fdca70be67c74151cea3846be7f73342d92c0090b62c1052e6790ad83f145"
        txOutRefIdx = 0

    scriptContextScriptInfo :: ScriptInfo
    scriptContextScriptInfo = SpendingScript txOutRef (Just datum)
      where
        datum :: Datum
        datum = Datum (toBuiltinData testLoanDatum)

testLoanDatum :: LoanDatum
testLoanDatum = askDatum
  where
    testCurSym :: CurrencySymbol
    testCurSym = CurrencySymbol "mysymbol"

    testTokName :: TokenName
    testTokName = TokenName "mytoken"

    askDatum :: LoanDatum
    askDatum =
      AskDatum
        { collateral = [(testCurSym, testTokName)]
        , askBeacon = (testCurSym, testTokName)
        , borrowerId = (testCurSym, testTokName)
        , loanAsset = (testCurSym, testTokName)
        , loanPrinciple = 10
        , loanTerm = 10
        }

testBeneficiaryPKH :: PubKeyHash
testBeneficiaryPKH = PubKeyHash ""
