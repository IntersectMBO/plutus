{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs            #-}
{-# LANGUAGE NamedFieldPuns   #-}
{-# LANGUAGE RankNTypes       #-}
{-# LANGUAGE TypeApplications #-}
-- |
module Plutus.PAB.Core.ContractInstance.BlockchainEnv(
  startNodeClient
  , processMockBlock
  , processChainSyncEvent
  , fromCardanoTxId
  ) where

import           Cardano.Api                            (BlockInMode (..), NetworkId)
import qualified Cardano.Api                            as C
import           Cardano.Node.Types                     (NodeMode (..))
import           Cardano.Protocol.Socket.Client         (ChainSyncEvent (..))
import qualified Cardano.Protocol.Socket.Client         as Client
import qualified Cardano.Protocol.Socket.Mock.Client    as MockClient
import qualified Data.Map                               as Map
import           Ledger                                 (Block, OnChainTx, Slot, TxId (..))
import           Ledger.AddressMap                      (AddressMap)
import qualified Ledger.AddressMap                      as AddressMap
import           Plutus.ChainIndex.TxIdState            (increaseDepth)
import           Plutus.PAB.Core.ContractInstance.STM   (BlockchainEnv (..), InstanceClientEnv (..), InstancesState,
                                                         OpenTxOutProducedRequest (..), OpenTxOutSpentRequest (..),
                                                         emptyBlockchainEnv)
import qualified Plutus.PAB.Core.ContractInstance.STM   as S
import           Plutus.Trace.Emulator.ContractInstance (IndexedBlock (..), indexBlock)
import           Plutus.V1.Ledger.Api                   (toBuiltin)

import           Control.Concurrent.STM                 (STM)
import qualified Control.Concurrent.STM                 as STM
import           Control.Lens
import           Control.Monad                          (forM_, unless, void, when)
import           Data.Foldable                          (foldl')
import           Data.Map                               (Map)
import           Ledger.TimeSlot                        (SlotConfig)
import           Plutus.ChainIndex                      (ChainIndexTx (..), ChainIndexTxOutputs (..), TxStatus (..),
                                                         TxValidity (..), citxTxId, fromOnChainTx)

-- | Connect to the node and write node updates to the blockchain
--   env.
startNodeClient ::
  FilePath -- ^ Socket to connect to node
  -> NodeMode -- ^ Whether to connect to real node or mock node
  -> SlotConfig -- ^ Slot config used by the node
  -> NetworkId -- ^ Cardano network ID
  -> InstancesState -- ^ In-memory state of running contract instances
  -> IO BlockchainEnv
startNodeClient socket mode slotConfig networkId instancesState = do
    env <- STM.atomically emptyBlockchainEnv
    case mode of
      MockNode ->
        void $ MockClient.runChainSync socket slotConfig
            (\block slot -> STM.atomically $ processMockBlock instancesState env block slot)
      AlonzoNode -> do
          let resumePoints = []
          void $ Client.runChainSync socket slotConfig networkId resumePoints
            (\block slot -> STM.atomically $ processChainSyncEvent env block slot)
    pure env

updateInstances :: IndexedBlock -> InstanceClientEnv -> STM ()
updateInstances IndexedBlock{ibUtxoSpent, ibUtxoProduced} InstanceClientEnv{ceUtxoSpentRequests, ceUtxoProducedRequests} = do
  forM_ (Map.intersectionWith (,) ibUtxoSpent ceUtxoSpentRequests) $ \(onChainTx, requests) ->
    traverse (\OpenTxOutSpentRequest{osrSpendingTx} -> STM.tryPutTMVar osrSpendingTx onChainTx) requests
  forM_ (Map.intersectionWith (,) ibUtxoProduced ceUtxoProducedRequests) $ \(txns, requests) ->
    traverse (\OpenTxOutProducedRequest{otxProducingTxns} -> STM.tryPutTMVar otxProducingTxns txns) requests

-- | Process a chain sync event that we receive from the alonzo node client
processChainSyncEvent :: BlockchainEnv -> ChainSyncEvent -> Slot -> STM ()
processChainSyncEvent blockchainEnv event _slot = case event of
  Resume _                                                -> pure () -- TODO: Handle resume
  RollForward  (BlockInMode (C.Block _ transactions) era) -> processBlock blockchainEnv transactions era
  RollBackward cp                                         -> rollback cp


rollback chainPoint = undefined

-- | Get transaction ID and validity from a cardano transaction in any era
txEvent :: forall era. C.Tx era -> C.EraInMode era C.CardanoMode -> (TxId, TxValidity)
txEvent (C.Tx body _) _ =
  let txi = fromCardanoTxId (C.getTxId @era body)
  in (txi, TxValid)  -- TODO: Validity for Alonzo transactions (not available in cardano-api yet (?))

fromCardanoTxId :: C.TxId -> TxId
fromCardanoTxId = TxId . toBuiltin . C.serialiseToRawBytes

-- | Get transaction ID and validity from an emulator transaction
txMockEvent :: ChainIndexTx -> (TxId, TxValidity)
txMockEvent tx =
  let validity = case tx of ChainIndexTx { _citxOutputs = ValidTx _ } -> TxValid
                            ChainIndexTx { _citxOutputs = InvalidTx } -> TxInvalid
   in (view citxTxId tx, validity)

-- | Update the blockchain env. with changes from a new block of cardano
--   transactions in any era
processBlock :: forall era. BlockchainEnv -> [C.Tx era] -> C.EraInMode era C.CardanoMode -> STM ()
processBlock BlockchainEnv{beTxChanges} transactions era = do
  STM.modifyTVar beTxChanges (fmap increaseDepth)
  unless (null transactions) $ do
    txStatusMap <- STM.readTVar beTxChanges
    let txStatusMap' = foldl' insertNewTx txStatusMap (flip txEvent era <$> transactions)
    STM.writeTVar beTxChanges txStatusMap'

insertNewTx :: Map TxId TxStatus -> (TxId, TxValidity) -> Map TxId TxStatus
insertNewTx oldMap (txi, txValidity) =
  oldMap & at txi ?~ newV
    where
      newV = TentativelyConfirmed 0 txValidity

-- | Go through the transactions in a block, updating the 'BlockchainEnv'
--   when any interesting addresses or transactions have changed.
processMockBlock :: InstancesState -> BlockchainEnv -> Block -> Slot -> STM ()
processMockBlock instancesState BlockchainEnv{beAddressMap, beTxChanges, beCurrentSlot} transactions slot = do
  STM.modifyTVar beTxChanges (fmap increaseDepth)
  lastSlot <- STM.readTVar beCurrentSlot
  when (slot > lastSlot) $ do
    STM.writeTVar beCurrentSlot slot
  unless (null transactions) $ do
    addressMap <- STM.readTVar beAddressMap
    let addressMap' = foldl' (processTx slot) addressMap transactions
    STM.writeTVar beAddressMap addressMap'

    txStatusMap <- STM.readTVar beTxChanges
    let txStatusMap' = foldl' insertNewTx txStatusMap (txMockEvent <$> fmap fromOnChainTx transactions)
    STM.writeTVar beTxChanges txStatusMap'

    instEnv <- S.instancesClientEnv instancesState
    updateInstances (indexBlock $ fmap fromOnChainTx transactions) instEnv

processTx :: Slot -> AddressMap -> OnChainTx -> AddressMap
processTx _ addressMap tx = addressMap' where
  -- TODO: Will be removed in a future issue
  addressMap' = AddressMap.updateAllAddresses tx addressMap
  -- TODO: updateInstances
  -- We need to switch to using 'ChainIndexTx' everyhwere first, though.
