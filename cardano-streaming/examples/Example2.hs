{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE OverloadedStrings   #-}

module Main where

import Cardano.Api qualified
import Cardano.Streaming (withChainSyncEventStream)
import Common (Options (Options, optionsChainPoint, optionsNetworkId, optionsSocketPath),
               parseOptions, printJson, workaround)
import Data.Aeson ((.=))
import Data.Aeson qualified as Aeson
import Ledger.Tx.CardanoAPI qualified
import Orphans qualified ()
import Streaming.Prelude qualified as S

--
-- Main
--

main :: IO ()
main = do
  Options{optionsSocketPath, optionsNetworkId, optionsChainPoint} <- parseOptions
  withChainSyncEventStream optionsSocketPath optionsNetworkId [optionsChainPoint] $
    printJson . S.map (fmap extractData)
 where
  extractData (Cardano.Api.BlockInMode (Cardano.Api.Block _header txs) eim) =
    flip map txs $ \tx@(Cardano.Api.Tx txBody _) ->
      let scriptData = Ledger.Tx.CardanoAPI.scriptDataFromCardanoTxBody txBody
          txId = Ledger.Tx.CardanoAPI.fromCardanoTxId $ Cardano.Api.getTxId txBody
          txOutRefs =
            Ledger.Tx.CardanoAPI.txOutRefs
              (workaround (Ledger.Tx.CardanoAPI.CardanoTx tx) eim)
       in Aeson.object
            [ "txId" .= txId
            , "txOutRefs" .= txOutRefs
            , "scriptData" .= scriptData
            ]
