{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs            #-}
{-# LANGUAGE LambdaCase       #-}
{-# LANGUAGE MonoLocalBinds   #-}
{-# LANGUAGE NamedFieldPuns   #-}
{-# LANGUAGE RankNTypes       #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators    #-}
-- |
module Plutus.PAB.Core.ContractInstance.BlockchainEnv(
  startNodeClient
  , ClientEnv(..)
  , processMockBlock
  , processChainSyncEvent
  , getClientEnv
  , fromCardanoTxId
  ) where

import           Cardano.Api                          (BlockInMode (..), NetworkId)
import qualified Cardano.Api                          as C
import           Cardano.Node.Types                   (NodeMode (..))
import           Cardano.Protocol.Socket.Client       (ChainSyncEvent (..))
import qualified Cardano.Protocol.Socket.Client       as Client
import qualified Cardano.Protocol.Socket.Mock.Client  as MockClient
import           Ledger                               (Address, Block, OnChainTx, Slot, TxId (..), eitherTx, txId)
import           Ledger.AddressMap                    (AddressMap)
import qualified Ledger.AddressMap                    as AddressMap
import           Plutus.Contract.Effects              (TxStatus (..), TxValidity (..), increaseDepth)
import           Plutus.PAB.Core.ContractInstance.STM (BlockchainEnv (..), InstancesState, emptyBlockchainEnv)
import qualified Plutus.PAB.Core.ContractInstance.STM as S

import           Control.Concurrent.STM               (STM)
import qualified Control.Concurrent.STM               as STM
import           Control.Lens
import           Control.Monad                        (foldM, forM_, unless, void, when)
import           Data.Foldable                        (foldl')
import           Data.Map                             (Map)
import           Data.Set                             (Set)
import           Ledger.TimeSlot                      (SlotConfig)
import           Wallet.Emulator.ChainIndex.Index     (ChainIndex, ChainIndexItem (..))
import qualified Wallet.Emulator.ChainIndex.Index     as Index

-- | Connect to the node and write node updates to the blockchain
--   env.
startNodeClient ::
  FilePath -- ^ Socket to connect to node
  -> NodeMode -- ^ Whether to connect to real node or mock node
  -> SlotConfig -- ^ Slot config used by the node
  -> NetworkId -- ^ Cardano network ID
  -> IO BlockchainEnv
startNodeClient socket mode slotConfig networkId = do
    env <- STM.atomically emptyBlockchainEnv
    case mode of
      MockNode ->
        void $ MockClient.runChainSync socket slotConfig
            (\block slot -> STM.atomically $ processMockBlock env block slot)
      AlonzoNode -> do
          let resumePoints = []
          void $ Client.runChainSync socket slotConfig networkId resumePoints
            (\block slot -> STM.atomically $ processChainSyncEvent env block slot)
    pure env

-- | Interesting addresses and transactions from all the
--   active instances.
data ClientEnv = ClientEnv{ceAddresses :: Set Address, ceTransactions :: Set TxId} deriving Eq

getClientEnv :: InstancesState -> STM ClientEnv
getClientEnv instancesState =
  ClientEnv
    <$> S.watchedAddresses instancesState
    <*> S.watchedTransactions instancesState

-- | Process a chain sync event that we receive from the alonzo node client
processChainSyncEvent :: BlockchainEnv -> ChainSyncEvent -> Slot -> STM ()
processChainSyncEvent blockchainEnv event _slot = case event of
  Resume _                                                -> pure () -- TODO: Handle resume
  RollForward  (BlockInMode (C.Block _ transactions) era) -> processBlock blockchainEnv transactions era
  RollBackward _cp                                        -> pure () -- TODO: Handle rollbacks

-- | Get transaction ID and validity from a cardano transaction in any era
txEvent :: forall era. C.Tx era -> C.EraInMode era C.CardanoMode -> (TxId, TxValidity)
txEvent (C.Tx body _) _ =
  let txi = fromCardanoTxId (C.getTxId @era body)
  in (txi, TxValid)  -- TODO: Validity for Alonzo transactions (not available in cardano-api yet (?))

fromCardanoTxId :: C.TxId -> TxId
fromCardanoTxId = TxId . C.serialiseToRawBytes

-- | Get transaction ID and validity from an emulator transaction
txMockEvent :: OnChainTx -> (TxId, TxValidity)
txMockEvent = eitherTx (\t -> (txId t, TxValid)) (\t -> (txId t, TxInvalid))

-- | Update the blockchain env. with changes from a new block of cardano
--   transactions in any era
processBlock :: forall era. BlockchainEnv -> [C.Tx era] -> C.EraInMode era C.CardanoMode -> STM ()
processBlock BlockchainEnv{beTxChanges} transactions era = do
  changes <- STM.readTVar beTxChanges
  forM_ changes $ \tv -> STM.modifyTVar tv increaseDepth
  unless (null transactions) $ do
    txStatusMap <- STM.readTVar beTxChanges
    txStatusMap' <- foldM insertNewTx txStatusMap (flip txEvent era <$> transactions)
    STM.writeTVar beTxChanges txStatusMap'

insertNewTx :: Map TxId (STM.TVar TxStatus) -> (TxId, TxValidity) -> STM (Map TxId (STM.TVar TxStatus))
insertNewTx oldMap (txi, txValidity) = do
  newV <- STM.newTVar (TentativelyConfirmed 0 txValidity)
  pure $ oldMap & at txi ?~ newV

-- | Go through the transactions in a block, updating the 'BlockchainEnv'
--   when any interesting addresses or transactions have changed.
processMockBlock :: BlockchainEnv -> Block -> Slot -> STM ()
processMockBlock BlockchainEnv{beAddressMap, beTxChanges, beCurrentSlot, beTxIndex} transactions slot = do
  changes <- STM.readTVar beTxChanges
  forM_ changes $ \tv -> STM.modifyTVar tv increaseDepth
  lastSlot <- STM.readTVar beCurrentSlot
  when (slot > lastSlot) $ do
    STM.writeTVar beCurrentSlot slot
  unless (null transactions) $ do
    addressMap <- STM.readTVar beAddressMap
    chainIndex <- STM.readTVar beTxIndex
    let (addressMap', chainIndex') = foldl' (processTx slot) (addressMap, chainIndex) transactions
    STM.writeTVar beAddressMap addressMap'
    STM.writeTVar beTxIndex chainIndex'

    txStatusMap <- STM.readTVar beTxChanges
    txStatusMap' <- foldM insertNewTx txStatusMap (txMockEvent <$> transactions)
    STM.writeTVar beTxChanges txStatusMap'

processTx :: Slot -> (AddressMap, ChainIndex) -> OnChainTx -> (AddressMap, ChainIndex)
processTx currentSlot (addressMap, chainIndex) tx = (addressMap', chainIndex') where
  tid = eitherTx txId txId tx
  addressMap' = AddressMap.updateAllAddresses tx addressMap
  chainIndex' =
    let itm = ChainIndexItem{ciSlot = currentSlot, ciTx = tx, ciTxId = tid } in
    Index.insert addressMap' itm chainIndex
