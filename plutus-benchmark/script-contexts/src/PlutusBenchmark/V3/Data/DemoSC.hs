{-# LANGUAGE BangPatterns      #-}
{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms   #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE ViewPatterns      #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:certify=DemoSCCert #-}

module PlutusBenchmark.V3.Data.DemoSC where

import PlutusLedgerApi.Data.V1 qualified as PlutusTx
import PlutusLedgerApi.Data.V3 (PubKeyHash (..), Redeemer (..), ScriptContext, TxId (..), TxInfo,
                                TxOut, always, emptyMintValue, mintValueMinted,
                                pattern CertifyingScript, pattern MintingScript,
                                pattern NoOutputDatum, pattern ProposingScript,
                                pattern RewardingScript, pattern ScriptContext,
                                pattern SpendingScript, pattern TxInfo, pattern TxOut,
                                pattern TxOutRef, pattern VotingScript, txInInfoOutRef,
                                txInfoCurrentTreasuryAmount, txInfoData, txInfoFee, txInfoId,
                                txInfoInputs, txInfoMint, txInfoOutputs, txInfoProposalProcedures,
                                txInfoRedeemers, txInfoReferenceInputs, txInfoSignatories,
                                txInfoTreasuryDonation, txInfoTxCerts, txInfoValidRange,
                                txInfoVotes, txInfoWdrl, txOutAddress, txOutDatum,
                                txOutReferenceScript, txOutValue)
import PlutusLedgerApi.V1.Data.Address
import PlutusLedgerApi.V1.Data.Value
import PlutusLedgerApi.V3.Data.MintValue (MintValue (..))
import PlutusTx qualified
import PlutusTx.Builtins qualified as PlutusTx
import PlutusTx.Data.AssocMap qualified as Map
import PlutusTx.Data.List qualified as List
import PlutusTx.Plugin ()
import PlutusTx.Prelude qualified as PlutusTx

-- From `Cardano.Ledger.Plutus.Preprocessor.Source.V3`.
purposeIsWellFormed :: ScriptContext -> PlutusTx.BuiltinUnit
purposeIsWellFormed = \case
  ScriptContext
    TxInfo
      { txInfoMint = infoMint
      , txInfoInputs = infoInputs
      , txInfoWdrl = infoWdrl
      , txInfoTxCerts = infoTxCerts
      , txInfoVotes = infoVotes
      }
    _redeemer
    scriptInfo -> PlutusTx.check $
      case scriptInfo of
        MintingScript cs ->
          Map.member cs . getValue $ mintValueMinted infoMint
        SpendingScript txOutRef mDatum ->
          case mDatum of
            Just _ -> False
            Nothing ->
              List.null $ List.filter ((txOutRef PlutusTx.==) . txInInfoOutRef) infoInputs
        RewardingScript cred ->
          Map.member cred infoWdrl
        CertifyingScript _idx txCert ->
          List.null $ List.filter (txCert PlutusTx.==) infoTxCerts
        VotingScript voter ->
          Map.member voter infoVotes
        ProposingScript _idx _propProc -> True

compiledPurposeIsWellFormed :: PlutusTx.CompiledCode (ScriptContext -> PlutusTx.BuiltinUnit)
compiledPurposeIsWellFormed = $$(PlutusTx.compile [||purposeIsWellFormed||])

mkPurposeIsWellFormedCode :: ScriptContext -> PlutusTx.CompiledCode PlutusTx.BuiltinUnit
mkPurposeIsWellFormedCode sc =
  compiledPurposeIsWellFormed `PlutusTx.unsafeApplyCode` PlutusTx.liftCodeDef sc
