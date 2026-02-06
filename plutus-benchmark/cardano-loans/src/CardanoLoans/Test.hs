{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE Strict #-}
{-# LANGUAGE NoImplicitPrelude #-}

module CardanoLoans.Test where

import PlutusTx
import PlutusTx.Prelude hiding ((<>))

import CardanoLoans.Validator (LoanDatum (..), LoanRedeemer (..), loanValidatorCode)
import PlutusLedgerApi.Test.ScriptContextBuilder.Builder
  ( buildScriptContext
  , withAddress
  , withInlineDatum
  , withOutRef
  , withOutput
  , withSigner
  , withSpendingScript
  , withTxOutAddress
  , withTxOutValue
  , withValidRange
  , withValue
  )
import PlutusLedgerApi.V1.Address (pubKeyHashAddress)
import PlutusLedgerApi.V1.Value qualified as Value
import PlutusLedgerApi.V3
import Prelude ((<>))

validatorCodeFullyApplied :: CompiledCode BuiltinUnit
validatorCodeFullyApplied =
  loanValidatorCode `unsafeApplyCode` liftCodeDef (toBuiltinData testScriptContext)

testScriptContext :: ScriptContext
testScriptContext =
  buildScriptContext
    ( withValidRange
        ( Interval
            (LowerBound (Finite 110) True)
            (UpperBound (Finite 1100) True)
        )
        <> withSigner testBeneficiaryPKH
        <> withSpendingScript
          (toBuiltinData CloseAsk)
          ( withOutRef txOutRef
              <> withAddress (pubKeyHashAddress testBeneficiaryPKH)
              <> withValue (Value.lovelaceValue 1000)
              <> withInlineDatum (toBuiltinData testLoanDatum)
          )
        <> withOutput
          ( withTxOutAddress (pubKeyHashAddress testBeneficiaryPKH)
              <> withTxOutValue (Value.lovelaceValue 1000)
          )
    )
  where
    txOutRef :: TxOutRef
    txOutRef = TxOutRef txOutRefId txOutRefIdx
      where
        txOutRefId = "058fdca70be67c74151cea3846be7f73342d92c0090b62c1052e6790ad83f145"
        txOutRefIdx = 0

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
