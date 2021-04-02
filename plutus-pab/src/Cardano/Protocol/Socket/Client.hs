{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs             #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE NamedFieldPuns    #-}
{-# LANGUAGE TypeFamilies      #-}

module Cardano.Protocol.Socket.Client where

import qualified Data.ByteString.Lazy                                as LBS
import           Data.Time.Units                                     (Second, TimeUnit, toMicroseconds)
import           Data.Void                                           (Void)

import           Control.Concurrent
import           Control.Concurrent.STM
import           Control.Monad.Catch                                 (catchAll)
import           Control.Tracer

import           Ouroboros.Network.Block                             (Point (..))
import qualified Ouroboros.Network.Protocol.ChainSync.Client         as ChainSync
import qualified Ouroboros.Network.Protocol.LocalTxSubmission.Client as TxSubmission

import           Ouroboros.Network.IOManager
import           Ouroboros.Network.Mux
import           Ouroboros.Network.NodeToNode
import           Ouroboros.Network.Protocol.Handshake.Codec
import           Ouroboros.Network.Protocol.Handshake.Unversioned
import           Ouroboros.Network.Protocol.Handshake.Version
import           Ouroboros.Network.Snocket
import           Ouroboros.Network.Socket

import           Cardano.Protocol.Socket.Type
import           Ledger                                              (Block, Slot (..), Tx (..))

-- | Client handler, used to communicate with the client thread.
data ClientHandler = ClientHandler
    { chInputQueue  :: TQueue Tx
    , chSocketPath  :: FilePath
    , chCurrentSlot :: IO Slot
    , chHandler     :: (Block -> Slot -> IO ())
    }

-- | Queue a transaction to be sent to the server.
queueTx ::
    ClientHandler
 -> Tx
 -> IO ()
queueTx ClientHandler { chInputQueue } tx =
    atomically (writeTQueue chInputQueue tx)

getCurrentSlot :: ClientHandler -> IO Slot
getCurrentSlot = chCurrentSlot

runClientNode :: FilePath
              -> SlotConfig
              -> (Block -> Slot -> IO ())
              -> IO ClientHandler
runClientNode socketPath slotConfig onNewBlock = do
    inputQueue  <- newTQueueIO
    let handle = ClientHandler { chInputQueue = inputQueue
                               , chSocketPath = socketPath
                               , chCurrentSlot = currentSlot slotConfig
                               , chHandler = onNewBlock
                               }

    _ <- forkIO $ withIOManager $ loop (1 :: Second) handle
    pure handle
    where
      loop :: TimeUnit a => a -> ClientHandler -> IOManager -> IO ()
      loop timeout ch@ClientHandler{chSocketPath, chInputQueue, chCurrentSlot, chHandler} iocp = do
        catchAll
          (connectToNode
            (localSnocket iocp socketPath)
            unversionedHandshakeCodec
            (cborTermVersionDataCodec unversionedProtocolDataCodec)
            nullNetworkConnectTracers
            acceptableVersion
            (unversionedProtocol (app chCurrentSlot chHandler chInputQueue))
            Nothing
            (localAddressFromPath chSocketPath))
          {- If we receive any error or disconnect, try to reconnect.
             This happens a lot on startup, until the server starts. -}
          (\_ -> do
               threadDelay (fromIntegral $ toMicroseconds timeout)
               loop timeout ch iocp)

      {- Application that communicates using 2 multiplexed protocols
         (ChainSync and TxSubmission). -}
      app :: (Block -> Slot -> IO ())
          -> TQueue Tx
          -> OuroborosApplication 'InitiatorMode addr
                                  LBS.ByteString IO () Void
      app onNewBlock' inputQueue =
        nodeApplication (chainSync onNewBlock') (txSubmission inputQueue)

      chainSync :: (Block -> Slot -> IO ())
                -> RunMiniProtocol 'InitiatorMode LBS.ByteString IO () Void
      chainSync onNewBlock' =
          InitiatorProtocolOnly $
          MuxPeer
            nullTracer
            codecChainSync
            (ChainSync.chainSyncClientPeer
               (chainSyncClient slotConfig onNewBlock'))

      txSubmission :: TQueue Tx
                   -> RunMiniProtocol 'InitiatorMode LBS.ByteString IO () Void
      txSubmission inputQueue =
          InitiatorProtocolOnly $
          MuxPeer
            nullTracer
            codecTxSubmission
            (TxSubmission.localTxSubmissionClientPeer
               (txSubmissionClient inputQueue))

-- | The client updates the application state when the protocol state changes.
chainSyncClient :: SlotConfig
                -> (Block -> Slot -> IO ())
                -> ChainSync.ChainSyncClient Block (Point Block) Tip IO ()
chainSyncClient slotConfig onNewBlock =
    ChainSync.ChainSyncClient $ pure requestNext
    where
      requestNext :: ChainSync.ClientStIdle Block (Point Block) Tip IO ()
      requestNext =
        ChainSync.SendMsgRequestNext
          handleNext
          (return handleNext)

      handleNext :: ChainSync.ClientStNext Block (Point Block) Tip IO ()
      handleNext =
        ChainSync.ClientStNext
        {
          ChainSync.recvMsgRollForward  = \block _ ->
            ChainSync.ChainSyncClient $ do
              slot <- currentSlot slotConfig
              onNewBlock block slot
              return requestNext
        , ChainSync.recvMsgRollBackward = error "Not supported."
        }

-- | The client updates the application state when the protocol state changes.
txSubmissionClient :: TQueue Tx
                   -> TxSubmission.LocalTxSubmissionClient Tx String IO ()
txSubmissionClient txQueue =
    TxSubmission.LocalTxSubmissionClient pushTxs
    where
      pushTxs :: IO (TxSubmission.LocalTxClientStIdle Tx String IO ())
      pushTxs = do
        header <- atomically $ readTQueue txQueue
        return $ TxSubmission.SendMsgSubmitTx
                   header
                   (const pushTxs) -- ignore rejects for now
