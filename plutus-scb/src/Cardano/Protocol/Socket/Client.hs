{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs             #-}
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
import           Ouroboros.Network.Protocol.Handshake.Type
import           Ouroboros.Network.Protocol.Handshake.Unversioned
import           Ouroboros.Network.Snocket
import           Ouroboros.Network.Socket

import           Cardano.Node.Types                                  (AppState)
import           Cardano.Protocol.Socket.Type
import           Ledger                                              (Block, Tx (..))

-- | Client configuration acts like a client handle.

data ClientConfig m =
    ClientConfig { ccSocketPath   :: FilePath      -- ^ Path of the socket used to communicate with the server.
                 , ccAppState     :: MVar AppState -- ^ Client application state.
                 , ccBlockHandler :: Block -> m () -- ^ Handler used to store the incoming blocks.
                 , ccTxQueue      :: TQueue Tx     -- ^ A queue used to send new transactions to the server.
                 }

-- | Forks and starts a new client node, returning the newly allocated thread id.
startClientNode :: ClientConfig IO
                -> IO ThreadId
startClientNode cfg =
    forkIO $ withIOManager $ \iocp ->
        connectToNode
          (localSnocket iocp (ccSocketPath cfg))
          unversionedHandshakeCodec
          cborTermVersionDataCodec
          nullNetworkConnectTracers
          (simpleSingletonVersions
            UnversionedProtocol
            (NodeToNodeVersionData $ NetworkMagic 0)
            (DictVersion nodeToNodeCodecCBORTerm)
            (\_peerid -> app))
          Nothing
          (localAddressFromPath (ccSocketPath cfg))

    where
      {- Application that communicates using 2 multiplexed protocols
         (ChainSync and TxSubmission, with BlockFetch coming soon). -}
      app :: OuroborosApplication 'InitiatorApp
                                  LBS.ByteString IO () Void
      app =
        nodeApplication chainSync txSubmission

      chainSync :: RunMiniProtocol 'InitiatorApp LBS.ByteString IO () Void
      chainSync =
          InitiatorProtocolOnly $
          MuxPeer
            (contramap show stdoutTracer)
            codecChainSync
            (ChainSync.chainSyncClientPeer
               (chainSyncClient (ccBlockHandler cfg)))

      txSubmission :: RunMiniProtocol 'InitiatorApp LBS.ByteString IO () Void
      txSubmission =
          InitiatorProtocolOnly $
          MuxPeer
            (contramap show stdoutTracer)
            codecTxSubmission
            (TxSubmission.localTxSubmissionClientPeer
               (txSubmissionClient (ccTxQueue cfg)))

-- | The client updates the application state when the protocol state changes.
chainSyncClient :: (Block -> IO ())
                -> ChainSync.ChainSyncClient Block Tip IO ()
chainSyncClient blockHandler =
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
              _ <- blockHandler block
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
