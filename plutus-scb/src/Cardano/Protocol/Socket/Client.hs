{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs             #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE TypeFamilies      #-}

module Cardano.Protocol.Socket.Client where

import qualified Data.ByteString.Lazy                                as LBS
import           Data.Void                                           (Void)

import           Control.Concurrent
import           Control.Concurrent.STM
import           Control.Tracer

import qualified Ouroboros.Network.Protocol.ChainSync.Client         as ChainSync
import qualified Ouroboros.Network.Protocol.LocalTxSubmission.Client as TxSubmission

import           Ouroboros.Network.IOManager
import           Ouroboros.Network.Magic
import           Ouroboros.Network.Mux
import           Ouroboros.Network.NodeToNode
import           Ouroboros.Network.Protocol.Handshake.Codec
import           Ouroboros.Network.Protocol.Handshake.Unversioned
import           Ouroboros.Network.Snocket
import           Ouroboros.Network.Socket

import           Cardano.Protocol.Socket.Type
import           Ledger                                              (Block, Tx (..))

-- | Client handler, used to communicate with the client thread.
data ClientHandler = ClientHandler {
        chOutputQueue :: TQueue Block,
        chInputQueue  :: TQueue Tx,
        chSocketPath  :: FilePath,
        chThreadId    :: ThreadId
    }

-- | Flush all the blocks that have accumulated on the queue.
--   It does not block.
flushBlocks ::
    ClientHandler
 -> IO [Block]
flushBlocks (ClientHandler outputQueue _ _ _) = go []
    where
      go :: [Block] -> IO [Block]
      go acc = atomically (tryReadTQueue outputQueue) >>= \case
          Nothing    -> pure (reverse acc)
          Just block -> go   (block : acc)

-- | Read the next block. It will block if no new block is
--   available.
getBlock ::
    ClientHandler
 -> IO Block
getBlock (ClientHandler outputQueue _ _ _) =
    atomically (readTQueue outputQueue)

-- | Queue a transaction to be sent to the server.
queueTx ::
    ClientHandler
 -> Tx
 -> IO ()
queueTx (ClientHandler _ inputQueue _ _) tx =
    atomically (writeTQueue inputQueue tx)

-- | Forks and starts a new client node, returning the newly allocated thread id.
runClientNode :: FilePath
              -> IO ClientHandler
runClientNode socketPath = do
    outputQueue <- newTQueueIO
    inputQueue  <- newTQueueIO
    threadId    <- forkIO $ withIOManager $ \iocp ->
        connectToNode
          (localSnocket iocp socketPath)
          unversionedHandshakeCodec
          cborTermVersionDataCodec
          nullNetworkConnectTracers
          (simpleSingletonVersions
            UnversionedProtocol
            (NodeToNodeVersionData $ NetworkMagic 0)
            (DictVersion nodeToNodeCodecCBORTerm)
            (app outputQueue inputQueue))
          Nothing
          (localAddressFromPath socketPath)
    pure ClientHandler {
        chOutputQueue = outputQueue,
        chInputQueue  = inputQueue,
        chSocketPath  = socketPath,
        chThreadId    = threadId
    }

    where
      {- Application that communicates using 2 multiplexed protocols
         (ChainSync and TxSubmission). -}
      app :: TQueue Block
          -> TQueue Tx
          -> OuroborosApplication 'InitiatorMode addr
                                  LBS.ByteString IO () Void
      app outputQueue inputQueue =
        nodeApplication (chainSync outputQueue) (txSubmission inputQueue)

      chainSync :: TQueue Block
                -> RunMiniProtocol 'InitiatorMode LBS.ByteString IO () Void
      chainSync outputQueue =
          InitiatorProtocolOnly $
          MuxPeer
            (contramap show stdoutTracer)
            codecChainSync
            (ChainSync.chainSyncClientPeer
               (chainSyncClient outputQueue))

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
chainSyncClient :: TQueue Block
                -> ChainSync.ChainSyncClient Block Tip IO ()
chainSyncClient outputQueue =
    ChainSync.ChainSyncClient $ pure requestNext
    where
      requestNext :: ChainSync.ClientStIdle Block Tip IO ()
      requestNext =
        ChainSync.SendMsgRequestNext
          handleNext
          (return handleNext)

      handleNext :: ChainSync.ClientStNext Block Tip IO ()
      handleNext =
        ChainSync.ClientStNext
        {
          ChainSync.recvMsgRollForward  = \block _ ->
            ChainSync.ChainSyncClient $ do
              atomically $ writeTQueue outputQueue block
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
