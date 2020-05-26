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

data ClientConfig m =
    ClientConfig { ccSocketPath   :: FilePath
                 , ccAppState     :: MVar AppState
                 , ccBlockHandler :: (Block -> m ())
                 , ccTxQueue      :: TQueue Tx
                 }

startClientNode :: ClientConfig IO
                -> IO ()
startClientNode cfg = withIOManager $ \iocp ->
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
      app :: OuroborosApplication 'InitiatorApp
                                  LBS.ByteString IO () Void
      app = nodeApplication chainSync txSubmission

      chainSync = undefined

      txSubmission = undefined

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
