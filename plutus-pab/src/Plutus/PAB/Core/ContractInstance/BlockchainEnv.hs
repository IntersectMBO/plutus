{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MonoLocalBinds   #-}
{-# LANGUAGE NamedFieldPuns   #-}
{-# LANGUAGE RankNTypes       #-}
{-# LANGUAGE TypeOperators    #-}
-- |
module Plutus.PAB.Core.ContractInstance.BlockchainEnv(
  startNodeClient
  , ClientEnv(..)
  , processBlock
  , getClientEnv
  ) where

import qualified Cardano.Protocol.Socket.Client       as Client
import           Ledger                               (Address, Block, OnChainTx, Slot, TxId, eitherTx, txId)
import           Ledger.AddressMap                    (AddressMap)
import qualified Ledger.AddressMap                    as AddressMap
import           Plutus.PAB.Core.ContractInstance.STM (BlockchainEnv (..), InstancesState, TxStatus (..),
                                                       emptyBlockchainEnv)
import qualified Plutus.PAB.Core.ContractInstance.STM as S

import           Control.Concurrent.STM               (STM)
import qualified Control.Concurrent.STM               as STM
import           Control.Lens
import           Control.Monad                        (unless, when)
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
  -> SlotConfig -- ^ Slot config used by the node
  -> IO BlockchainEnv
startNodeClient socket slotConfig = do
    env <- STM.atomically emptyBlockchainEnv
    _ <- Client.runChainSync socket slotConfig
            (\block slot -> STM.atomically $ processBlock env block slot)
    pure env

-- | Interesting addresses and transactions from all the
--   active instances.
data ClientEnv = ClientEnv{ceAddresses :: Set Address, ceTransactions :: Set TxId} deriving Eq

getClientEnv :: InstancesState -> STM ClientEnv
getClientEnv instancesState =
  ClientEnv
    <$> S.watchedAddresses instancesState
    <*> S.watchedTransactions instancesState

-- | Go through the transactions in a block, updating the 'BlockchainEnv'
--   when any interesting addresses or transactions have changed.
processBlock :: BlockchainEnv -> Block -> Slot -> STM ()
processBlock BlockchainEnv{beAddressMap, beTxChanges, beCurrentSlot, beTxIndex} transactions slot = do
  lastSlot <- STM.readTVar beCurrentSlot
  when (slot > lastSlot) $ do
    STM.modifyTVar beTxChanges (fmap S.increaseDepth)
    STM.writeTVar beCurrentSlot slot
  unless (null transactions) $ do
    addressMap <- STM.readTVar beAddressMap
    chainIndex <- STM.readTVar beTxIndex
    txStatusMap <- STM.readTVar beTxChanges
    let (addressMap', txStatusMap', chainIndex') = foldl' (processTx slot) (addressMap, txStatusMap, chainIndex) transactions
    STM.writeTVar beAddressMap addressMap'
    STM.writeTVar beTxChanges txStatusMap'
    STM.writeTVar beTxIndex chainIndex'


processTx :: Slot -> (AddressMap, Map TxId TxStatus, ChainIndex) -> OnChainTx -> (AddressMap, Map TxId TxStatus, ChainIndex)
processTx currentSlot (addressMap, txStatusMap, chainIndex) tx = (addressMap', txStatusMap', chainIndex') where
  tid = eitherTx txId txId tx
  addressMap' = AddressMap.updateAllAddresses tx addressMap
  chainIndex' =
    let itm = ChainIndexItem{ciSlot = currentSlot, ciTx = tx, ciTxId = tid } in
    Index.insert addressMap' itm chainIndex
  txStatusMap' = txStatusMap & at tid .~ Just (TentativelyConfirmed 0)
