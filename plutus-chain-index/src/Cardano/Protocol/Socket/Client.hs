{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DeriveAnyClass      #-}
{-# LANGUAGE DerivingStrategies  #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE NamedFieldPuns      #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeFamilies        #-}

module Cardano.Protocol.Socket.Client where

import           Control.Concurrent
import           Control.Monad.Catch                         (Handler (..), SomeException (..))
import           Data.Aeson                                  (FromJSON, ToJSON)
import           Data.Text                                   (Text, pack)
import           GHC.Generics                                (Generic)

import           Cardano.Api                                 (BlockInMode (..), CardanoMode, ChainPoint (..),
                                                              ChainTip (..), ConsensusModeParams (..),
                                                              LocalChainSyncClient (..), LocalNodeClientProtocols (..),
                                                              LocalNodeClientProtocolsInMode, LocalNodeConnectInfo (..),
                                                              NetworkId, connectToLocalNode)
import           Cardano.BM.Data.Trace                       (Trace)
import           Cardano.BM.Data.Tracer                      (ToObject (..))
import           Cardano.BM.Trace                            (logDebug, logWarning)
import           Control.Retry                               (fibonacciBackoff, recovering, skipAsyncExceptions)
import           Control.Tracer                              (nullTracer)
import           Ledger.TimeSlot                             (SlotConfig, currentSlot)
import           Ouroboros.Network.IOManager
import qualified Ouroboros.Network.Protocol.ChainSync.Client as ChainSync

import           Cardano.Protocol.Socket.Type                hiding (Tip)
import           Ledger                                      (Slot (..))
import           Plutus.ChainIndex.Compatibility             (fromCardanoPoint, fromCardanoTip)
import           Plutus.ChainIndex.Types                     (Point, Tip)

data ChainSyncHandle event = ChainSyncHandle
    { cshCurrentSlot :: IO Slot
    , cshHandler     :: event -> Slot -> IO ()
    }

data ChainSyncEvent =
    Resume       !ChainPoint
  | RollForward  !(BlockInMode CardanoMode) !ChainTip
  | RollBackward !ChainPoint !ChainTip

{- | The `Slot` parameter here represents the `current` slot as computed from the
     current time. There is also the slot where the block was published, which is
     available from the `ChainSyncEvent`.

     Currently we are using this current slot everywhere, which is why I leave it
     here, as a parameter.
-}
type ChainSyncCallback = ChainSyncEvent -> Slot -> IO ()

data ClientMsg =
    Disconnected Text
  | Resumed Point
  | RolledForward Tip
  | RolledBackward Point
  deriving stock (Eq, Show, Generic)
  deriving anyclass (FromJSON, ToJSON, ToObject)

getCurrentSlot
  :: forall block.
     ChainSyncHandle block
  -> IO Slot
getCurrentSlot = cshCurrentSlot

-- | Run the chain sync protocol to get access to the current slot number.
runChainSync'
  :: FilePath
  -> SlotConfig
  -> NetworkId
  -> [ChainPoint]
  -> IO (ChainSyncHandle ChainSyncEvent)
runChainSync' socketPath slotConfig networkId resumePoints =
  runChainSync socketPath nullTracer slotConfig networkId resumePoints (\_ _ -> pure ())

runChainSync
  :: FilePath
  -> Trace IO ClientMsg
  -> SlotConfig
  -> NetworkId
  -> [ChainPoint]
  -> ChainSyncCallback
  -> IO (ChainSyncHandle ChainSyncEvent)
runChainSync socketPath trace slotConfig networkId resumePoints chainSyncEventHandler = do
    let handle = ChainSyncHandle {
          cshCurrentSlot = currentSlot slotConfig,
          cshHandler = chainSyncEventHandler }

    _ <- forkIO $ withIOManager $ \_ ->
           recovering
             (fibonacciBackoff 500)
             (skipAsyncExceptions ++
               [(\_ -> Handler $ \(err :: SomeException) -> do
                   logWarning trace (Disconnected $ pack $ show err)
                   pure True )])
             (\_ -> connectToLocalNode
                      localNodeConnectInfo
                      localNodeClientProtocols)

    pure handle
    where
      localNodeConnectInfo = LocalNodeConnectInfo {
        localConsensusModeParams = CardanoModeParams epochSlots,
        localNodeNetworkId = networkId,
        localNodeSocketPath = socketPath }
      localNodeClientProtocols :: LocalNodeClientProtocolsInMode CardanoMode
      localNodeClientProtocols = LocalNodeClientProtocols {
        localChainSyncClient =
          LocalChainSyncClient $
            chainSyncClient trace slotConfig resumePoints chainSyncEventHandler,
        localTxSubmissionClient = Nothing,
        localStateQueryClient = Nothing }

-- | The client updates the application state when the protocol state changes.
chainSyncClient
  :: Trace IO ClientMsg
  -> SlotConfig
  -> [ChainPoint]
  -> ChainSyncCallback
  -> ChainSync.ChainSyncClient (BlockInMode CardanoMode) ChainPoint ChainTip IO ()
chainSyncClient trace slotConfig [] chainSyncEventHandler =
  chainSyncClient trace slotConfig [ChainPointAtGenesis] chainSyncEventHandler
chainSyncClient trace slotConfig resumePoints chainSyncEventHandler =
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
                   logDebug trace (Resumed $ fromCardanoPoint chainPoint)
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
          ChainSync.recvMsgRollForward  = \block tip ->
            ChainSync.ChainSyncClient $ do
              slot <- currentSlot slotConfig
              logDebug trace (RolledForward $ fromCardanoTip tip)
              chainSyncEventHandler (RollForward block tip) slot
              pure requestNext
        , ChainSync.recvMsgRollBackward = \point tip ->
            ChainSync.ChainSyncClient $ do
              slot <- currentSlot slotConfig
              logDebug trace (RolledBackward $ fromCardanoPoint point)
              chainSyncEventHandler (RollBackward point tip) slot
              pure requestNext
        }

