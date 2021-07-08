{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs             #-}
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

import           Ledger.TimeSlot                                     (SlotConfig, currentSlot)
import           Ouroboros.Network.IOManager
import           Ouroboros.Network.Mux
import           Ouroboros.Network.NodeToNode                        hiding (chainSyncMiniProtocolNum,
                                                                      txSubmissionMiniProtocolNum)
import           Ouroboros.Network.Protocol.Handshake.Codec
import           Ouroboros.Network.Protocol.Handshake.Unversioned
import           Ouroboros.Network.Protocol.Handshake.Version
import           Ouroboros.Network.Snocket
import           Ouroboros.Network.Socket

import           Cardano.Protocol.Socket.Type
import           Ledger                                              (Block, Slot (..), Tx (..))

data ChainSyncHandle = ChainSyncHandle
    { cshCurrentSlot :: IO Slot
    , cshHandler     :: Block -> Slot -> IO ()
    }

newtype TxSendHandle = TxSendHandle
    { tshQueue :: TQueue Tx }

-- | Queue a transaction to be sent to the server.
queueTx ::
    TxSendHandle
 -> Tx
 -> IO ()
queueTx TxSendHandle { tshQueue } tx =
    atomically (writeTQueue tshQueue tx)

getCurrentSlot :: ChainSyncHandle -> IO Slot
getCurrentSlot = cshCurrentSlot

-- | Run the chain sync protocol to get access to the current slot number.
runChainSync' :: FilePath
              -> SlotConfig
              -> IO ChainSyncHandle
runChainSync' socketPath slotConfig =
  runChainSync socketPath slotConfig (\_ _ -> pure ())

runChainSync :: FilePath
             -> SlotConfig
             -> (Block -> Slot -> IO ())
             -> IO ChainSyncHandle
runChainSync socketPath slotConfig onNewBlock = do
    let handle = ChainSyncHandle { cshCurrentSlot = currentSlot slotConfig
                                 , cshHandler = onNewBlock
                                 }

    _ <- forkIO $ withIOManager $ loop (1 :: Second) handle
    pure handle
    where
      loop :: TimeUnit a => a -> ChainSyncHandle -> IOManager -> IO ()
      loop timeout ch@ChainSyncHandle{ cshHandler } iocp = do
        catchAll
          (connectToNode
            (localSnocket iocp socketPath)
            unversionedHandshakeCodec
            noTimeLimitsHandshake
            (cborTermVersionDataCodec unversionedProtocolDataCodec)
            nullNetworkConnectTracers
            acceptableVersion
            (unversionedProtocol $ app cshHandler)
            Nothing
            (localAddressFromPath socketPath))
          {- If we receive any error or disconnect, try to reconnect.
             This happens a lot on startup, until the server starts. -}
          (\_ -> do
               threadDelay (fromIntegral $ toMicroseconds timeout)
               loop timeout ch iocp)

      {- Application that communicates using 2 multiplexed protocols
         (ChainSync and TxSubmission). -}
      app :: (Block -> Slot -> IO ())
          -> OuroborosApplication 'InitiatorMode addr
                                  LBS.ByteString IO () Void
      app onNewBlock' =
        mkApplication [(chainSyncMiniProtocolNum, chainSync onNewBlock')]

      chainSync :: (Block -> Slot -> IO ())
                -> RunMiniProtocol 'InitiatorMode LBS.ByteString IO () Void
      chainSync onNewBlock' =
          InitiatorProtocolOnly $
          MuxPeer
            nullTracer
            codecChainSync
            (ChainSync.chainSyncClientPeer
               (chainSyncClient slotConfig onNewBlock'))

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

runTxSender :: FilePath
            -> IO TxSendHandle
runTxSender socketPath = do
    inputQueue  <- newTQueueIO
    let handle = TxSendHandle { tshQueue = inputQueue }

    _ <- forkIO $ withIOManager $ loop (1 :: Second) handle
    pure handle
    where
      loop :: TimeUnit a => a -> TxSendHandle -> IOManager -> IO ()
      loop timeout ch@TxSendHandle{ tshQueue } iocp = do
        catchAll
          (connectToNode
            (localSnocket iocp socketPath)
            unversionedHandshakeCodec
            noTimeLimitsHandshake
            (cborTermVersionDataCodec unversionedProtocolDataCodec)
            nullNetworkConnectTracers
            acceptableVersion
            (unversionedProtocol (app tshQueue))
            Nothing
            (localAddressFromPath socketPath))
          {- If we receive any error or disconnect, try to reconnect.
             This happens a lot on startup, until the server starts. -}
          (\_ -> do
               threadDelay (fromIntegral $ toMicroseconds timeout)
               loop timeout ch iocp)

      {- Application that communicates using 2 multiplexed protocols
         (ChainSync and TxSubmission). -}
      app :: TQueue Tx
          -> OuroborosApplication 'InitiatorMode addr
                                  LBS.ByteString IO () Void
      app inputQueue =
        mkApplication [(txSubmissionMiniProtocolNum, txSubmission inputQueue)]


      txSubmission :: TQueue Tx
                   -> RunMiniProtocol 'InitiatorMode LBS.ByteString IO () Void
      txSubmission inputQueue =
          InitiatorProtocolOnly $
          MuxPeer
            (showTracing stdoutTracer)
            codecTxSubmission
            (TxSubmission.localTxSubmissionClientPeer
               (txSubmissionClient inputQueue))

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
