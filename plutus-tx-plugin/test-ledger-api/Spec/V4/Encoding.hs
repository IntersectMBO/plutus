{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -fplugin Plinth.Plugin #-}
{-# OPTIONS_GHC -fplugin-opt Plinth.Plugin:defer-errors #-}

module Spec.V4.Encoding (tests) where

import Plinth.Plugin (plinthc)
import PlutusLedgerApi.Data.V4 qualified as DataV4
import PlutusLedgerApi.V4 qualified as V4
import PlutusTx.List qualified as PlutusList
import PlutusTx.Prelude qualified as PlutusTx
import PlutusTx.Test (assertResult)
import Test.Tasty (TestTree)
import Test.Tasty.Extras

tests :: TestTree
tests =
  runTestNested ["test-ledger-api", "Spec", "V4", "Encoding"] . pure . testNestedGhc $
    [ assertResult "protected address wrapper" $
        plinthc
          ( let value = V4.AddressProtected (V4.ScriptCredential (V4.ScriptHash "recipient")) Nothing
                decoded = PlutusTx.unsafeFromBuiltinData @DataV4.Address (PlutusTx.toBuiltinData value)
             in case decoded of
                  DataV4.AddressProtected (DataV4.ScriptCredential hash) Nothing ->
                    hash PlutusTx.== V4.ScriptHash "recipient"
                      && DataV4.isProtectedAddress decoded
                      && PlutusTx.toBuiltinData decoded PlutusTx.== PlutusTx.toBuiltinData value
                  _ -> False
          )
    , assertResult "receiving purpose and info wrappers" $
        plinthc
          ( let output =
                  V4.TxOut
                    (V4.AddressProtected (V4.ScriptCredential (V4.ScriptHash "recipient")) Nothing)
                    mempty
                    V4.NoOutputDatum
                    Nothing
                purpose = V4.Receiving (V4.ScriptHash "recipient") 3
                info =
                  PlutusTx.unsafeFromBuiltinData @DataV4.ScriptInfo
                    (PlutusTx.toBuiltinData (V4.ReceivingScript 3 output))
             in case PlutusTx.unsafeFromBuiltinData @DataV4.ScriptPurpose (PlutusTx.toBuiltinData purpose) of
                  DataV4.Receiving hash index -> case info of
                    DataV4.ReceivingScript infoIndex resolved ->
                      hash PlutusTx.== V4.ScriptHash "recipient"
                        && index PlutusTx.== 3
                        && infoIndex PlutusTx.== index
                        && PlutusTx.toBuiltinData resolved PlutusTx.== PlutusTx.toBuiltinData output
                    _ -> False
                  _ -> False
          )
    , assertResult "protected output selection keeps body indexes in both interfaces" $
        plinthc
          ( let recipient = V4.ScriptHash "recipient"
                ordinary = V4.TxOut (V4.Address (V4.ScriptCredential recipient) Nothing) mempty V4.NoOutputDatum Nothing
                protected =
                  V4.TxOut
                    (V4.AddressProtected (V4.ScriptCredential recipient) Nothing)
                    mempty
                    V4.NoOutputDatum
                    Nothing
                other =
                  V4.TxOut
                    (V4.AddressProtected (V4.ScriptCredential (V4.ScriptHash "other")) Nothing)
                    mempty
                    V4.NoOutputDatum
                    Nothing
                info =
                  V4.TxInfo
                    { V4.txInfoId = V4.TxId "transaction"
                    , V4.txInfoSubTxIx = Nothing
                    , V4.txInfoInputs = []
                    , V4.txInfoReferenceInputs = []
                    , V4.txInfoOutputs = [ordinary, protected, other, protected]
                    , V4.txInfoMint = V4.emptyMintValue
                    , V4.txInfoTxCerts = []
                    , V4.txInfoWithdrawals = V4.unsafeFromList []
                    , V4.txInfoDirectDeposits = V4.unsafeFromList []
                    , V4.txInfoAccountBalanceIntervals = V4.AccountBalanceIntervals (V4.unsafeFromList [])
                    , V4.txInfoValidRange = V4.POSIXTimeRange Nothing Nothing
                    , V4.txInfoGuards = []
                    , V4.txInfoRequiredTopLevelGuards = V4.unsafeFromList []
                    , V4.txInfoRedeemers = V4.unsafeFromList []
                    , V4.txInfoData = V4.unsafeFromList []
                    , V4.txInfoVotes = V4.unsafeFromList []
                    , V4.txInfoProposalProcedures = []
                    , V4.txInfoCurrentTreasuryAmount = Nothing
                    , V4.txInfoTreasuryDonation = V4.Lovelace 0
                    }
                backed = PlutusTx.unsafeFromBuiltinData @DataV4.TxInfo (PlutusTx.toBuiltinData info)
                context1 =
                  V4.ScriptContext
                    info
                    (V4.Redeemer (PlutusTx.toBuiltinData (1 :: Integer)))
                    (V4.ReceivingScript 1 protected)
                    recipient
                context3 =
                  V4.ScriptContext
                    info
                    (V4.Redeemer (PlutusTx.toBuiltinData (3 :: Integer)))
                    (V4.ReceivingScript 3 protected)
                    recipient
                backedContext3 = PlutusTx.unsafeFromBuiltinData @DataV4.ScriptContext (PlutusTx.toBuiltinData context3)
             in PlutusList.map PlutusTx.fst (V4.protectedOutputsAt recipient info) PlutusTx.== [1, 3]
                  && PlutusList.map PlutusTx.fst (DataV4.protectedOutputsAt recipient backed) PlutusTx.== [1, 3]
                  && PlutusTx.toBuiltinData context1 PlutusTx./= PlutusTx.toBuiltinData context3
                  && PlutusTx.toBuiltinData (V4.Receiving recipient 1)
                    PlutusTx./= PlutusTx.toBuiltinData (V4.Receiving recipient 3)
                  && case DataV4.scriptContextScriptInfo backedContext3 of
                    DataV4.ReceivingScript index resolved ->
                      index PlutusTx.== 3
                        && PlutusTx.toBuiltinData resolved PlutusTx.== PlutusTx.toBuiltinData protected
                        && PlutusTx.toBuiltinData (DataV4.scriptContextRedeemer backedContext3)
                          PlutusTx.== PlutusTx.toBuiltinData (3 :: Integer)
                    _ -> False
          )
    , assertResult "transaction reference wrapper" $
        plinthc
          ( let value = V4.TxOutRef (V4.TxId "transaction") 2
             in case PlutusTx.fromBuiltinData @V4.TxOutRef (PlutusTx.toBuiltinData value) of
                  Nothing -> False
                  Just decoded ->
                    V4.txOutRefId decoded PlutusTx.== V4.TxId "transaction"
                      && V4.txOutRefIdx decoded PlutusTx.== 2
          )
    , assertResult "rational wrapper" $
        plinthc
          ( case PlutusTx.fromBuiltinData @V4.Rational (PlutusTx.toBuiltinData ([2, 4] :: [Integer])) of
              Nothing -> False
              Just decoded ->
                V4.numerator decoded PlutusTx.== 1
                  && V4.denominator decoded PlutusTx.== 2
                  && PlutusTx.toBuiltinData decoded PlutusTx.== PlutusTx.toBuiltinData ([1, 2] :: [Integer])
          )
    , assertResult "nested data-backed proposal" $
        plinthc
          ( let value =
                  V4.ProposalProcedure
                    (V4.Lovelace 10)
                    (V4.PubKeyCredential (V4.PubKeyHash "key"))
                    (V4.HardForkInitiation Nothing (V4.ProtocolVersion 11 0))
                decoded = PlutusTx.unsafeFromBuiltinData @DataV4.ProposalProcedure (PlutusTx.toBuiltinData value)
             in case DataV4.ppGovernanceAction decoded of
                  DataV4.HardForkInitiation Nothing version ->
                    DataV4.pvMajor version PlutusTx.== 11
                      && DataV4.pvMinor version PlutusTx.== 0
                      && PlutusTx.toBuiltinData decoded PlutusTx.== PlutusTx.toBuiltinData value
                  _ -> False
          )
    ]
