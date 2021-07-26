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
import           Ouroboros.Network.IOManager
import qualified Ouroboros.Network.Protocol.ChainSync.Client as ChainSync

import           Cardano.Protocol.Socket.Type                hiding (Tip)
import           Ledger                                      (Slot (..))

data ChainSyncHandle event = ChainSyncHandle
    { cshCurrentSlot :: IO Slot
    , cshHandler     :: event -> Slot -> IO ()
    }

data ChainSyncEvent =
    Resume !ChainPoint
  | RollForward !(BlockInMode CardanoMode)

{- | The `Slot` parameter here represents the `current` slot as computed from the
     current time. There is also the slot where the block was published, which is
     available from the `ChainSyncEvent`.

     Currently we are using this current slot everywhere, which is why I leave it
     here, as a parameter.
-}
type ChainSyncCallback = ChainSyncEvent -> Slot -> IO ()

getCurrentSlot
  :: forall block.
     ChainSyncHandle block
  -> IO Slot
getCurrentSlot = cshCurrentSlot

-- | Run the chain sync protocol to get access to the current slot number.
runChainSync'
  :: FilePath
  -> SlotConfig
  -> [ChainPoint]
  -> IO (ChainSyncHandle ChainSyncEvent)
runChainSync' socketPath slotConfig resumePoints =
  runChainSync socketPath slotConfig resumePoints (\_ _ -> pure ())

runChainSync
  :: FilePath
  -> SlotConfig
  -> [ChainPoint]
  -> ChainSyncCallback
  -> IO (ChainSyncHandle ChainSyncEvent)
runChainSync socketPath slotConfig resumePoints chainSyncEventHandler = do
    let handle = ChainSyncHandle {
          cshCurrentSlot = currentSlot slotConfig,
          cshHandler = chainSyncEventHandler }

    _ <- forkIO $ withIOManager $ loop (1 :: Second)
    pure handle
    where
      localNodeConnectInfo = LocalNodeConnectInfo {
        localConsensusModeParams = CardanoModeParams epochSlots,
        localNodeNetworkId = cfgNetworkId,
        localNodeSocketPath = socketPath }
      localNodeClientProtocols :: LocalNodeClientProtocolsInMode CardanoMode
      localNodeClientProtocols = LocalNodeClientProtocols {
        localChainSyncClient =
          LocalChainSyncClient $
            chainSyncClient slotConfig resumePoints chainSyncEventHandler,
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
  -> [ChainPoint]
  -> ChainSyncCallback
  -> ChainSync.ChainSyncClient (BlockInMode CardanoMode) ChainPoint ChainTip IO ()
chainSyncClient slotConfig [] chainSyncEventHandler =
  chainSyncClient slotConfig [ChainPointAtGenesis] chainSyncEventHandler
chainSyncClient slotConfig resumePoints chainSyncEventHandler =
    ChainSync.ChainSyncClient $ pure initialise
    where
      initialise :: ChainSync.ClientStIdle (BlockInMode CardanoMode) ChainPoint ChainTip IO ()
      initialise =
        ChainSync.SendMsgFindIntersect resumePoints $
          ChainSync.ClientStIntersect {
            ChainSync.recvMsgIntersectFound    =
              \chainPoint _ ->
                 ChainSync.ChainSyncClient $ do
                   slot <- currentSlot slotConfig
                   chainSyncEventHandler (Resume chainPoint) slot
                   pure requestNext,
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
              chainSyncEventHandler (RollForward block) slot
              pure requestNext
        , ChainSync.recvMsgRollBackward = \_     _ ->
            ChainSync.ChainSyncClient $ pure requestNext
        }

