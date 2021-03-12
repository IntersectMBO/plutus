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
  , updateInterestingAddresses
  ) where

import qualified Cardano.Protocol.Socket.Client       as Client
import           Ledger                               (Address, Block, Slot, Tx, TxId, txId)
import           Ledger.AddressMap                    (AddressMap)
import qualified Ledger.AddressMap                    as AddressMap
import           Plutus.PAB.Core.ContractInstance.STM (BlockchainEnv (..), InstancesState, TxStatus (..),
                                                       emptyBlockchainEnv)
import qualified Plutus.PAB.Core.ContractInstance.STM as S

import           Control.Concurrent                   (forkIO)
import           Control.Concurrent.STM               (STM)
import qualified Control.Concurrent.STM               as STM
import           Control.Lens
import           Control.Monad                        (guard, when)
import           Data.Foldable                        (foldl')
import           Data.Map                             (Map)
import           Data.Set                             (Set)
import qualified Data.Set                             as Set
import           Wallet.Emulator.ChainIndex.Index     (ChainIndex, ChainIndexItem (..))
import qualified Wallet.Emulator.ChainIndex.Index     as Index

-- | Connect to the node and write node updates to the blockchain
--   env.
startNodeClient ::
  FilePath -- ^ Socket to connect to node
  -> InstancesState
  -> IO BlockchainEnv
startNodeClient socket instancesState =  do
    env <- STM.atomically emptyBlockchainEnv
    _ <- Client.runClientNode socket (\block -> STM.atomically . processBlock env block)
    _ <- forkIO (clientEnvLoop env instancesState)
    pure env

-- | Interesting addresses and transactions from all the
--   active instances.
data ClientEnv = ClientEnv{ceAddresses :: Set Address, ceTransactions :: Set TxId} deriving Eq

initialClientEnv :: ClientEnv
initialClientEnv = ClientEnv mempty mempty

getClientEnv :: InstancesState -> STM ClientEnv
getClientEnv instancesState =
  ClientEnv
    <$> S.watchedAddresses instancesState
    <*> S.watchedTransactions instancesState

-- | Wait until the 'ClientEnv' has changed.
nextClientEnv :: InstancesState -> ClientEnv -> STM ClientEnv
nextClientEnv instancesState currentEnv = do
  newEnv <- getClientEnv instancesState
  guard $ newEnv /= currentEnv
  pure newEnv

clientEnvLoop :: BlockchainEnv -> InstancesState -> IO ()
clientEnvLoop env instancesState = go initialClientEnv where
  go currentEnv = do
    STM.atomically (updateInterestingAddresses env currentEnv)
    STM.atomically (nextClientEnv instancesState currentEnv) >>= go

updateInterestingAddresses :: BlockchainEnv -> ClientEnv -> STM ()
updateInterestingAddresses BlockchainEnv{beAddressMap} ClientEnv{ceAddresses} = do
  STM.modifyTVar beAddressMap (AddressMap.addAddresses (Set.toList ceAddresses))

-- | Go through the transactions in a block, updating the 'BlockchainEnv'
--   when any interesting addresses or transactions have changed.
processBlock :: BlockchainEnv -> Block -> Slot -> STM ()
processBlock BlockchainEnv{beAddressMap, beTxChanges, beCurrentSlot, beTxIndex} transactions slot = do
  addressMap <- STM.readTVar beAddressMap
  chainIndex <- STM.readTVar beTxIndex
  txStatusMap <- STM.readTVar beTxChanges
  let (addressMap', txStatusMap', chainIndex') = foldl' (processTx slot) (addressMap, txStatusMap, chainIndex) transactions
  STM.writeTVar beAddressMap addressMap'
  STM.writeTVar beTxChanges txStatusMap'
  STM.writeTVar beTxIndex chainIndex'
  lastSlot <- STM.readTVar beCurrentSlot
  when (slot /= lastSlot) (STM.writeTVar beCurrentSlot slot)

processTx :: Slot -> (AddressMap, Map TxId TxStatus, ChainIndex) -> Tx -> (AddressMap, Map TxId TxStatus, ChainIndex)
processTx currentSlot (addressMap, txStatusMap, chainIndex) tx = (addressMap', txStatusMap', chainIndex') where
  addressMap' = AddressMap.updateAddresses tx addressMap
  chainIndex' =
    let itm = ChainIndexItem{ciSlot = currentSlot, ciTx = tx, ciTxId = txId tx} in
    Index.insert addressMap' itm chainIndex
  txStatusMap' = txStatusMap & at (txId tx) .~ Just TentativelyConfirmed
