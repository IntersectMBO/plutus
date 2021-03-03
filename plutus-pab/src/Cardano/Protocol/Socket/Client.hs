{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs             #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE NamedFieldPuns    #-}
{-# LANGUAGE TypeFamilies      #-}

module Cardano.Protocol.Socket.Client where

import qualified Data.ByteString.Lazy                                as LBS
import           Data.Void                                           (Void)

import           Control.Concurrent
import           Control.Concurrent.STM
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
    , chThreadId    :: ThreadId
    , chCurrentSlot :: MVar Slot
    }

-- | Queue a transaction to be sent to the server.
queueTx ::
    ClientHandler
 -> Tx
 -> IO ()
queueTx ClientHandler { chInputQueue } tx =
    atomically (writeTQueue chInputQueue tx)

getCurrentSlot ::
     ClientHandler
  -> IO Slot
getCurrentSlot ClientHandler { chCurrentSlot } =
    readMVar chCurrentSlot

-- | Forks and starts a new client node, returning the newly allocated thread id.
runClientNode :: FilePath
              -> (Block -> Slot -> IO ())
              -> IO ClientHandler
runClientNode socketPath onNewBlock = do
    inputQueue  <- newTQueueIO
    -- Right now we synchronise the whole blockchain so we can initialise the first
    -- slot to be 0. This will change when we start looking for intersection points.
    mSlot    <- newMVar (Slot 0)
    threadId <- forkIO $ withIOManager $ \iocp ->
        connectToNode
          (localSnocket iocp socketPath)
          unversionedHandshakeCodec
          (cborTermVersionDataCodec unversionedProtocolDataCodec)
          nullNetworkConnectTracers
          acceptableVersion
          (unversionedProtocol (app mSlot onNewBlock inputQueue))
          Nothing
          (localAddressFromPath socketPath)
    pure ClientHandler { chInputQueue  = inputQueue
                       , chSocketPath  = socketPath
                       , chThreadId    = threadId
                       , chCurrentSlot = mSlot
                       }

    where
      {- Application that communicates using 2 multiplexed protocols
         (ChainSync and TxSubmission). -}
      app :: MVar Slot
          -> (Block -> Slot -> IO ())
          -> TQueue Tx
          -> OuroborosApplication 'InitiatorMode addr
                                  LBS.ByteString IO () Void
      app mSlot onNewBlock' inputQueue =
        nodeApplication (chainSync mSlot onNewBlock') (txSubmission inputQueue)

      chainSync :: MVar Slot
                -> (Block -> Slot -> IO ())
                -> RunMiniProtocol 'InitiatorMode LBS.ByteString IO () Void
      chainSync mSlot onNewBlock' =
          InitiatorProtocolOnly $
          MuxPeer
            (contramap show stdoutTracer)
            codecChainSync
            (ChainSync.chainSyncClientPeer
               (chainSyncClient mSlot onNewBlock'))

      txSubmission :: TQueue Tx
                   -> RunMiniProtocol 'InitiatorMode LBS.ByteString IO () Void
      txSubmission inputQueue =
          InitiatorProtocolOnly $
          MuxPeer
            (contramap show stdoutTracer)
            codecTxSubmission
            (TxSubmission.localTxSubmissionClientPeer
               (txSubmissionClient inputQueue))

-- | The client updates the application state when the protocol state changes.
chainSyncClient :: MVar Slot
                -> (Block -> Slot -> IO ())
                -> ChainSync.ChainSyncClient Block (Point Block) Tip IO ()
chainSyncClient mSlot onNewBlock =
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
              currentSlot <- takeMVar mSlot
              onNewBlock block (currentSlot + 1)
              putMVar mSlot (currentSlot + 1)
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
