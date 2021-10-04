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

import           Cardano.Api                            (BlockInMode (..), ChainPoint (..), NetworkId)
import qualified Cardano.Api                            as C
import           Cardano.Node.Types                     (NodeMode (..))
import           Cardano.Protocol.Socket.Client         (ChainSyncEvent (..))
import qualified Cardano.Protocol.Socket.Client         as Client
import qualified Cardano.Protocol.Socket.Mock.Client    as MockClient
import qualified Data.Map                               as Map
import           Data.Monoid                            (Last (..), Sum (..))
import           Ledger                                 (Block, OnChainTx, Slot, TxId (..))
import           Ledger.AddressMap                      (AddressMap)
import qualified Ledger.AddressMap                      as AddressMap
import           Plutus.PAB.Core.ContractInstance.STM   (BlockchainEnv (..), InstanceClientEnv (..), InstancesState,
                                                         OpenTxOutProducedRequest (..), OpenTxOutSpentRequest (..),
                                                         emptyBlockchainEnv)
import qualified Plutus.PAB.Core.ContractInstance.STM   as S
import           Plutus.Trace.Emulator.ContractInstance (IndexedBlock (..), indexBlock)
import           Plutus.V1.Ledger.Api                   (toBuiltin)

import           Control.Concurrent.STM                 (STM)
import qualified Control.Concurrent.STM                 as STM
import           Control.Lens
import           Control.Monad                          (forM_, void, when)
import           Control.Tracer                         (nullTracer)
import           Data.Foldable                          (foldl')
import           Ledger.TimeSlot                        (SlotConfig)
import           Plutus.ChainIndex                      (BlockNumber (..), ChainIndexTx (..), ChainIndexTxOutputs (..),
                                                         InsertUtxoFailed (..), InsertUtxoSuccess (..),
                                                         RollbackFailed (..), RollbackResult (..), Tip (..),
                                                         TxConfirmedState (..), TxIdState (..), TxValidity (..),
                                                         UtxoState (..), blockId, citxTxId, fromOnChainTx, insert,
                                                         utxoState)
import           Plutus.ChainIndex.Compatibility        (fromCardanoBlockHeader, fromCardanoPoint)
import           Plutus.ChainIndex.TxIdState            (rollback)

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
            (\block slot -> handleSyncAction $ processMockBlock instancesState env block slot)
      AlonzoNode -> do
          let resumePoints = []
          void $ Client.runChainSync socket nullTracer slotConfig networkId resumePoints
            (\block slot -> handleSyncAction $ processChainSyncEvent env block slot)
    pure env

-- | Deal with sync action failures from running this STM action. For now, we
-- deal with them by simply calling `error`; i.e. the application exits.
handleSyncAction :: STM (Either SyncActionFailure ()) -> IO ()
handleSyncAction action = STM.atomically action >>= either (error . show) pure

updateInstances :: IndexedBlock -> InstanceClientEnv -> STM ()
updateInstances IndexedBlock{ibUtxoSpent, ibUtxoProduced} InstanceClientEnv{ceUtxoSpentRequests, ceUtxoProducedRequests} = do
  forM_ (Map.intersectionWith (,) ibUtxoSpent ceUtxoSpentRequests) $ \(onChainTx, requests) ->
    traverse (\OpenTxOutSpentRequest{osrSpendingTx} -> STM.tryPutTMVar osrSpendingTx onChainTx) requests
  forM_ (Map.intersectionWith (,) ibUtxoProduced ceUtxoProducedRequests) $ \(txns, requests) ->
    traverse (\OpenTxOutProducedRequest{otxProducingTxns} -> STM.tryPutTMVar otxProducingTxns txns) requests

-- | Process a chain sync event that we receive from the alonzo node client
processChainSyncEvent :: BlockchainEnv -> ChainSyncEvent -> Slot -> STM (Either SyncActionFailure ())
processChainSyncEvent blockchainEnv event _slot = do
  case event of
      Resume _                                                       -> pure $ Right () -- TODO: Handle resume
      RollForward  (BlockInMode (C.Block header transactions) era) _ -> processBlock header blockchainEnv transactions era
      RollBackward chainPoint _                                      -> runRollback blockchainEnv chainPoint

data SyncActionFailure
  = RollbackFailure RollbackFailed
  | InsertUtxoStateFailure InsertUtxoFailed
  deriving (Show)

-- | Roll back the chain to the given ChainPoint and slot.
runRollback :: BlockchainEnv -> ChainPoint -> STM (Either SyncActionFailure ())
runRollback BlockchainEnv{beTxChanges} chainPoint = do
  txIdStateIndex <- STM.readTVar beTxChanges

  let point = fromCardanoPoint chainPoint
      rs    = rollback point txIdStateIndex

  case rs of
    Left e                                -> pure $ Left (RollbackFailure e)
    Right RollbackResult{rolledBackIndex} -> Right <$> STM.writeTVar beTxChanges rolledBackIndex

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
processBlock :: forall era. C.BlockHeader
             -> BlockchainEnv
             -> [C.Tx era]
             -> C.EraInMode era C.CardanoMode
             -> STM (Either SyncActionFailure ())
processBlock header env transactions era =
  if null transactions
     then pure $ Right ()
     else do
        let tip = fromCardanoBlockHeader header
        updateTransactionState tip env (flip txEvent era <$> transactions)

-- | For the given transactions, perform the updates in the TxIdState, and
-- also record that a new block has been processed.
updateTransactionState
  :: Foldable t
  => Tip
  -> BlockchainEnv
  -> t (TxId, TxValidity)
  -> STM (Either SyncActionFailure ())
updateTransactionState tip BlockchainEnv{beTxChanges, beCurrentBlock} xs = do
    txIdStateIndex <- STM.readTVar beTxChanges
    let txIdState = _usTxUtxoData $ utxoState $ txIdStateIndex
    blockNumber <- STM.readTVar beCurrentBlock
    let txIdState' = foldl' (insertNewTx blockNumber) txIdState xs
        is  = insert (UtxoState txIdState' tip) txIdStateIndex
    case is of
      Right InsertUtxoSuccess{newIndex=newTxIdState} -> do
        STM.writeTVar beTxChanges newTxIdState
        STM.writeTVar beCurrentBlock (succ blockNumber)
        pure $ Right ()
      Left e -> pure $ Left $ InsertUtxoStateFailure e

insertNewTx :: BlockNumber -> TxIdState -> (TxId, TxValidity) -> TxIdState
insertNewTx blockNumber TxIdState{txnsConfirmed, txnsDeleted} (txi, txValidity) =
  let newConfirmed = txnsConfirmed & at txi ?~ newV
   in TxIdState (txnsConfirmed <> newConfirmed) txnsDeleted
    where
      -- New state; we rely on the monoid instance to make this agree with any
      -- existing transactions already present (but perhaps rolled back.)
      newV = TxConfirmedState
              { timesConfirmed = Sum 1
              , blockAdded     = Last (Just blockNumber)
              , validity       = Last (Just txValidity)
              }

-- | Go through the transactions in a block, updating the 'BlockchainEnv'
--   when any interesting addresses or transactions have changed.
processMockBlock :: InstancesState -> BlockchainEnv -> Block -> Slot -> STM (Either SyncActionFailure ())
processMockBlock instancesState env@BlockchainEnv{beAddressMap, beCurrentSlot, beCurrentBlock} transactions slot = do
  lastSlot <- STM.readTVar beCurrentSlot
  when (slot > lastSlot) $ do
    STM.writeTVar beCurrentSlot slot

  if null transactions
     then pure $ Right ()
     else do
      addressMap <- STM.readTVar beAddressMap
      let addressMap' = foldl' (processTx slot) addressMap transactions
      STM.writeTVar beAddressMap addressMap'
      blockNumber <- STM.readTVar beCurrentBlock

      instEnv <- S.instancesClientEnv instancesState
      updateInstances (indexBlock $ fmap fromOnChainTx transactions) instEnv


      let tip = Tip { tipSlot = slot
                    , tipBlockId = blockId transactions
                    , tipBlockNo = blockNumber
                    }

      updateTransactionState tip env (txMockEvent <$> fmap fromOnChainTx transactions)

processTx :: Slot -> AddressMap -> OnChainTx -> AddressMap
processTx _ addressMap tx = addressMap' where
  -- TODO: Will be removed in a future issue
  addressMap' = AddressMap.updateAllAddresses tx addressMap
  -- TODO: updateInstances
  -- We need to switch to using 'ChainIndexTx' everyhwere first, though.
