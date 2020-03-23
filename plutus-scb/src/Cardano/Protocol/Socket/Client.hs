{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs             #-}
{-# LANGUAGE TypeFamilies      #-}

module Cardano.Protocol.Socket.Client where

import qualified Data.ByteString.Lazy                                as LBS
import           Data.Functor.Contravariant                          (contramap)
import           Data.Void                                           (Void)

import           Control.Concurrent
import           Control.Concurrent.STM
import           Control.Lens
import           Control.Monad.Freer                                 (Eff)
import qualified Control.Monad.Freer                                 as Eff
import qualified Control.Monad.Freer.Extra.Log                       as Eff
import           Control.Monad.Freer.Extras                          (handleZoomedState)
import qualified Control.Monad.Freer.State                           as Eff
import qualified Control.Monad.Freer.Writer                          as Eff
import           Control.Monad.Logger
import           Control.Monad.Reader
import           Control.Tracer

import qualified Cardano.Protocol.Socket.Puppet.Client               as Puppet
import qualified Ouroboros.Network.Protocol.ChainSync.Client         as ChainSync
import qualified Ouroboros.Network.Protocol.LocalTxSubmission.Client as TxSubmission

import           Codec.Serialise                                     (DeserialiseFailure)
import           Network.Mux.Types                                   (AppType (..))
import           Ouroboros.Network.Magic
import           Ouroboros.Network.Mux
import           Ouroboros.Network.NodeToNode
import           Ouroboros.Network.Protocol.Handshake.Type
import           Ouroboros.Network.Protocol.Handshake.Version
import           Ouroboros.Network.Socket

import           Cardano.Protocol.Node
import           Cardano.Protocol.Socket.Type
import           Ledger                                              (Block, Tx (..))
import           Plutus.SCB.Core
import           Plutus.SCB.EventLog
import           Wallet.Emulator.Chain                               hiding (ChainEvent)

startClientNode :: FilePath
                -> Connection
                -> MVar ClientStreamProjection
                -> PuppetHandle
                -> IO ()
startClientNode sockAddr connection state endpoint =
    connectToNode
      cborTermVersionDataCodec
      nullNetworkConnectTracers
      (simpleSingletonVersions (0 :: Int)
                               (NodeToNodeVersionData $ NetworkMagic 0)
                               (DictVersion nodeToNodeCodecCBORTerm) app)
      Nothing
      (mkLocalSocketAddrInfo sockAddr)

    where
      app :: OuroborosApplication 'InitiatorApp
                                  ConnectionId
                                  NodeToClientPtcls
                                  IO LBS.ByteString () Void
      app = simpleInitiatorApplication protocols

      protocols :: NodeToClientPtcls -> MuxPeer ConnectionId
                                                DeserialiseFailure
                                                IO LBS.ByteString ()
      protocols ChainSyncWithBlocksPtcl =
          MuxPeer
            (contramap show stdoutTracer)
            codecChainSync
            (ChainSync.chainSyncClientPeer (chainSyncClient connection state))

      protocols LocalTxSubmissionPtcl =
          MuxPeer
            (contramap show stdoutTracer)
            codecTxSubmission
            (TxSubmission.localTxSubmissionClientPeer (txSubmissionClient connection state (txInputQueue endpoint)))

      protocols PuppetPtcl =
          MuxPeer
            (contramap show stdoutTracer)
            codecPuppet
            (Puppet.puppetClientPeer (puppetClient (ctlRequest endpoint) (ctlResponse endpoint)))

puppetClient :: TQueue PuppetRequest
             -> TQueue PuppetResponse
             -> Puppet.PuppetClient ChainState Block IO ()
puppetClient req res =
    Puppet.PuppetClient processNextRequest
  where
    processNextRequest :: IO (Puppet.PuppetClientStIdle ChainState Block IO ())
    processNextRequest = do
      cmd <- atomically $ readTQueue req
      case cmd of
        RequestState      ->
          return $ Puppet.SendMsgRequestState
            (\state -> atomically (writeTQueue res (ResponseState state))
                         >> processNextRequest)
        RequestValidation ->
          return $ Puppet.SendMsgValidate
            (\block -> atomically (writeTQueue res (Validated block))
                         >> processNextRequest)

chainSyncClient :: Connection
                -> MVar ClientStreamProjection
                -> ChainSync.ChainSyncClient Block Tip IO ()
chainSyncClient connection clientPrj =
    ChainSync.ChainSyncClient sendLocalState
    where
      sendLocalState :: IO (ChainSync.ClientStIdle Block Tip IO ())
      sendLocalState  = do
        cs <- readMVar clientPrj
        return $ ChainSync.SendMsgFindIntersect
          (wrapLocalState $ cs ^. chainState)
          receiveRemoteState

      receiveRemoteState :: ChainSync.ClientStIntersect Block Tip IO ()
      receiveRemoteState =
        ChainSync.ClientStIntersect
        { ChainSync.recvMsgIntersectFound    = \point _ ->
            ChainSync.ChainSyncClient $ do
              _ <- runNodeClientEffects connection clientPrj $
                resumeLocalState point
              return requestNext
        , ChainSync.recvMsgIntersectNotFound = error "Not supported."
        }

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
              _ <- runNodeClientEffects connection clientPrj
                processBlock
              return requestNext
        , ChainSync.recvMsgRollBackward = error "Not supported."
        }

txSubmissionClient :: Connection
                   -> MVar ClientStreamProjection
                   -> TQueue Tx
                   -> TxSubmission.LocalTxSubmissionClient Tx String IO ()
txSubmissionClient connection clientPrj txInput =
    TxSubmission.LocalTxSubmissionClient pushTxs
    where
      pushTxs :: IO (TxSubmission.LocalTxClientStIdle Tx String IO ())
      pushTxs = do
        header <- atomically $ readTQueue txInput
        _ <- runNodeClientEffects connection clientPrj $
          queueTx header
        return $ TxSubmission.SendMsgSubmitTx
                   header
                   (const pushTxs) -- ignore rejects for now

type NodeClientM = (ReaderT Connection (LoggingT IO))

runNodeClientEffects ::
    Connection
 -> MVar ClientStreamProjection
 -> Eff (NodeClientEffects NodeClientM) a
 -> IO a
runNodeClientEffects connection st action = do
  prj            <- liftIO $ takeMVar st
  (((result, ncEvents), cEvents), prj') <- liftIO
    $ runStderrLoggingT
    $ flip runReaderT connection
    $ Eff.runM
    $ Eff.runStderrLog
    $ Eff.runState prj
    $ handleEventLog
    $ Eff.runWriter
    $ Eff.runWriter
    -- Note: The chain state in the node client *should not* be
    --       updated directly through the state, but through
    --       refreshing the projection to avoid cases where we directly
    --       modify the projection in inconsistent ways.
    --       As it is now, the algebra can cause unexpected behaviors, I think.
    --
    --       .. In the current code, it is not updated directly, since the
    --       only instance  where that happens is when calling `processBlock` which is
    --       a control call for the mocked node server (and we are interpreting for
    --       the node client).
    --       But we can write an algebra term that would trigger this behavior
    --       and everything will happily compile.
    --
    -- Meta: Is it really a good idea to have an algebra that is *partially* interpreted
    --       in different components? Maybe we should decide not to have that and audit
    --       the code to find such instances.
    $ Eff.interpret (handleZoomedState chainState)
    $ handleChain' action
  liftIO $ putMVar st prj'
  return result
