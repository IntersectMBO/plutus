{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE NamedFieldPuns      #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeFamilies        #-}

module Cardano.Protocol.Socket.Client where

import qualified Data.ByteString.Lazy                        as LBS
import           Data.Time.Units                             (Second, TimeUnit, toMicroseconds)
import           Data.Void                                   (Void)

import           Control.Concurrent
import           Control.Monad.Catch                         (catchAll)
import           Control.Tracer

import           Ouroboros.Network.Block                     (Point (..), Tip (..))
import qualified Ouroboros.Network.Protocol.ChainSync.Client as ChainSync

import           Cardano.Slotting.Slot                       (WithOrigin (..))
import           Ledger.TimeSlot                             (SlotConfig, currentSlot)
import           Ouroboros.Consensus.Cardano.Block           (CardanoBlock)
import           Ouroboros.Consensus.Network.NodeToClient    (Codecs' (..))
import           Ouroboros.Consensus.Shelley.Protocol        (StandardCrypto)
import           Ouroboros.Network.IOManager
import           Ouroboros.Network.Mux
import           Ouroboros.Network.NodeToClient              (NodeToClientProtocols (..), connectTo,
                                                              versionedNodeToClientProtocols)
import           Ouroboros.Network.Snocket
import           Ouroboros.Network.Socket

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
  -> IO (ChainSyncHandle CBlock)
runChainSync' socketPath slotConfig =
  runChainSync socketPath slotConfig (\_ _ -> pure ())

runChainSync
  :: FilePath
  -> SlotConfig
  -> (CBlock -> Slot -> IO ())
  -> IO (ChainSyncHandle CBlock)
runChainSync socketPath slotConfig onNewBlock = do
    let handle = ChainSyncHandle { cshCurrentSlot = currentSlot slotConfig
                                 , cshHandler = onNewBlock
                                 }

    _ <- forkIO $ withIOManager $ loop (1 :: Second) handle
    pure handle
    where
      loop :: forall a. TimeUnit a
           => a
           -> ChainSyncHandle CBlock
           -> IOManager
           -> IO ()
      loop timeout ch@ChainSyncHandle{ cshHandler } iocp = do
        catchAll
          (connectTo
            (localSnocket iocp socketPath)
            nullNetworkConnectTracers
            (versionedNodeToClientProtocols
              nodeToClientVersion
              nodeToClientVersionData
              (\_ _ -> nodeToClientProtocols cshHandler))
            socketPath)
          {- If we receive any error or disconnect, try to reconnect.
             This happens a lot on startup, until the server starts. -}
          (\_ -> do
               threadDelay (fromIntegral $ toMicroseconds timeout)
               loop timeout ch iocp)

      nodeToClientProtocols
        :: (CBlock -> Slot -> IO ())
        -> NodeToClientProtocols 'InitiatorMode LBS.ByteString IO () Void
      nodeToClientProtocols blockHandler =
        NodeToClientProtocols
          { localChainSyncProtocol = chainSync blockHandler
          , localTxSubmissionProtocol = doNothingInitiatorProtocol
          , localStateQueryProtocol = doNothingInitiatorProtocol
          }

      chainSync
        :: (CBlock -> Slot -> IO ())
        -> RunMiniProtocol 'InitiatorMode LBS.ByteString IO () Void
      chainSync onNewBlock' =
          InitiatorProtocolOnly $
          MuxPeer
            nullTracer
            (cChainSyncCodec nodeToClientCodecs)
            (ChainSync.chainSyncClientPeer
               (chainSyncClient slotConfig onNewBlock'))

-- | The client updates the application state when the protocol state changes.
chainSyncClient
  :: SlotConfig
  -> (CBlock -> Slot -> IO ())
  -> ChainSync.ChainSyncClient CBlock (Point CBlock) (Tip CBlock) IO ()
chainSyncClient slotConfig handleBlock =
    ChainSync.ChainSyncClient $ pure initialise
    where
      initialise :: ChainSync.ClientStIdle CBlock (Point CBlock) (Tip CBlock) IO ()
      initialise =
        ChainSync.SendMsgFindIntersect [Point Origin] $
          ChainSync.ClientStIntersect {
            ChainSync.recvMsgIntersectFound    =
              \_ _ -> ChainSync.ChainSyncClient $ pure requestNext,
            ChainSync.recvMsgIntersectNotFound =
              \_   -> ChainSync.ChainSyncClient $ pure requestNext
          }

      requestNext :: ChainSync.ClientStIdle CBlock (Point CBlock) (Tip CBlock) IO ()
      requestNext =
        ChainSync.SendMsgRequestNext
          handleNext
          (return handleNext)

      handleNext :: ChainSync.ClientStNext CBlock (Point CBlock) (Tip CBlock) IO ()
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

