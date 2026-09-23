{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -fplugin Plinth.Plugin #-}
{-# OPTIONS_GHC -fplugin-opt Plinth.Plugin:defer-errors #-}

module Spec.V4.Encoding (tests) where

import Plinth.Plugin (plinthc)
import PlutusLedgerApi.Data.V4 qualified as DataV4
import PlutusLedgerApi.V4 qualified as V4
import PlutusTx.Prelude qualified as PlutusTx
import PlutusTx.Test (assertResult)
import Test.Tasty (TestTree)
import Test.Tasty.Extras

tests :: TestTree
tests =
  runTestNested ["test-ledger-api", "Spec", "V4", "Encoding"] . pure . testNestedGhc $
    [ assertResult "transaction reference wrapper" $
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
