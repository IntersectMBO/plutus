{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE NamedFieldPuns      #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeFamilies        #-}

module Cardano.Protocol.Socket.Client where

import           Control.Concurrent
import           Control.Monad.Catch                         (catchAll)
import           Data.Time.Units                             (Second, TimeUnit, toMicroseconds)

import           Cardano.Api                                 (BlockInMode (..), CardanoMode, ChainPoint (..),
                                                              ChainTip (..), ConsensusModeParams (..),
                                                              LocalChainSyncClient (..), LocalNodeClientProtocols (..),
                                                              LocalNodeClientProtocolsInMode, LocalNodeConnectInfo (..),
                                                              connectToLocalNode)
import           Ledger.TimeSlot                             (SlotConfig, currentSlot)
import           Ouroboros.Consensus.Cardano.Block           (CardanoBlock)
import           Ouroboros.Consensus.Shelley.Protocol        (StandardCrypto)
import           Ouroboros.Network.IOManager
import qualified Ouroboros.Network.Protocol.ChainSync.Client as ChainSync

import           Cardano.Protocol.Socket.Type                hiding (Tip)
import           Ledger                                      (Slot (..))

data ChainSyncHandle block = ChainSyncHandle
    { cshCurrentSlot :: IO Slot
    , cshHandler     :: block -> Slot -> IO ()
    }

type CBlock = CardanoBlock StandardCrypto

getCurrentSlot
  :: ChainSyncHandle CBlock
  -> IO Slot
getCurrentSlot = cshCurrentSlot

-- | Run the chain sync protocol to get access to the current slot number.
runChainSync'
  :: FilePath
  -> SlotConfig
  -> IO (ChainSyncHandle (BlockInMode CardanoMode))
runChainSync' socketPath slotConfig =
  runChainSync socketPath slotConfig (\_ _ -> pure ())

runChainSync
  :: FilePath
  -> SlotConfig
  -> (BlockInMode CardanoMode -> Slot -> IO ())
  -> IO (ChainSyncHandle (BlockInMode CardanoMode))
runChainSync socketPath slotConfig onNewBlock = do
    let handle = ChainSyncHandle {
          cshCurrentSlot = currentSlot slotConfig,
          cshHandler = onNewBlock }

    _ <- forkIO $ withIOManager $ loop (1 :: Second)
    pure handle
    where
      localNodeConnectInfo = LocalNodeConnectInfo {
        localConsensusModeParams = CardanoModeParams epochSlots,
        localNodeNetworkId = cfgNetworkId,
        localNodeSocketPath = socketPath }
      localNodeClientProtocols :: LocalNodeClientProtocolsInMode CardanoMode
      localNodeClientProtocols = LocalNodeClientProtocols {
        localChainSyncClient = LocalChainSyncClient (chainSyncClient slotConfig onNewBlock),
        localTxSubmissionClient = Nothing,
        localStateQueryClient = Nothing }
      loop :: forall a. TimeUnit a
           => a
           -> IOManager
           -> IO ()
      loop timeout iocp = do
        catchAll
          (connectToLocalNode
             localNodeConnectInfo
             localNodeClientProtocols)
          (\_ -> do
               threadDelay (fromIntegral $ toMicroseconds timeout)
               loop timeout iocp)
-- | The client updates the application state when the protocol state changes.
chainSyncClient
  :: SlotConfig
  -> (BlockInMode CardanoMode -> Slot -> IO ())
  -> ChainSync.ChainSyncClient (BlockInMode CardanoMode) ChainPoint ChainTip IO ()
chainSyncClient slotConfig handleBlock =
    ChainSync.ChainSyncClient $ pure initialise
    where
      initialise :: ChainSync.ClientStIdle (BlockInMode CardanoMode) ChainPoint ChainTip IO ()
      initialise =
        ChainSync.SendMsgFindIntersect [ChainPointAtGenesis] $
          ChainSync.ClientStIntersect {
            ChainSync.recvMsgIntersectFound    =
              \_ _ -> ChainSync.ChainSyncClient $ pure requestNext,
            ChainSync.recvMsgIntersectNotFound =
              \_   -> ChainSync.ChainSyncClient $ pure requestNext
          }

      requestNext :: ChainSync.ClientStIdle (BlockInMode CardanoMode) ChainPoint ChainTip IO ()
      requestNext =
        ChainSync.SendMsgRequestNext
          handleNext
          (return handleNext)

      handleNext :: ChainSync.ClientStNext (BlockInMode CardanoMode) ChainPoint ChainTip IO ()
      handleNext =
        ChainSync.ClientStNext
        {
          ChainSync.recvMsgRollForward  = \block _ ->
            ChainSync.ChainSyncClient $ do
              slot <- currentSlot slotConfig
              handleBlock block slot
              pure requestNext
        , ChainSync.recvMsgRollBackward = \_     _ ->
            ChainSync.ChainSyncClient $ pure requestNext
        }

