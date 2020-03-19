{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE DeriveAnyClass    #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs             #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TypeFamilies      #-}

module Cardano.Protocol.Socket.Client where

import qualified Data.ByteString.Lazy                                as LBS
import           Data.Functor.Contravariant                          (contramap)
import           Data.List                                           (findIndex)
import           Data.Time.Units                                     (Second, toMicroseconds)
import           Data.Void                                           (Void)

import           Control.Concurrent
import           Control.Concurrent.STM
import           Control.Lens
import           Control.Monad.Freer                                 (Eff)
import           Control.Monad.Logger
import           Control.Monad.Reader
import           Control.Tracer

import           Eventful.Aggregate                                  (Aggregate (..))
import           Eventful.Projection                                 (GlobalStreamProjection, Projection (..),
                                                                      StreamProjection (..), globalStreamProjection)
import           Eventful.Store.Class

import qualified Cardano.Protocol.Socket.Puppet.Client               as Puppet
import qualified Ouroboros.Network.Protocol.ChainSync.Client         as ChainSync
import qualified Ouroboros.Network.Protocol.LocalTxSubmission.Client as TxSubmission

import           Cardano.Slotting.Slot                               (SlotNo (..), WithOrigin (..))
import           Codec.Serialise                                     (DeserialiseFailure)
import           Network.Mux.Types                                   (AppType (..))
import           Ouroboros.Network.Block                             (Point (..))
import           Ouroboros.Network.Magic
import           Ouroboros.Network.Mux
import           Ouroboros.Network.NodeToNode
import qualified Ouroboros.Network.Point                             as Point
import           Ouroboros.Network.Protocol.Handshake.Type
import           Ouroboros.Network.Protocol.Handshake.Version
import           Ouroboros.Network.Socket

import           Cardano.Protocol.Socket.Type

import           Cardano.Protocol.Node
import           Ledger                                              (Block, Slot (..), Tx (..))
import qualified Ledger.Index                                        as Index
import           Plutus.SCB.Core
import           Plutus.SCB.Events
import           Plutus.SCB.Query                                    (nullProjection)
import           Wallet.Emulator.Chain                               hiding (ChainEvent)

startClientNode :: FilePath
                -> Connection
                -> MVar ClientState
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
                -> MVar ClientState
                -> ChainSync.ChainSyncClient Block Tip IO ()
chainSyncClient connection clientState =
    ChainSync.ChainSyncClient sendLocalState
    where
      sendLocalState :: IO (ChainSync.ClientStIdle Block Tip IO ())
      sendLocalState  = do
        cs <- readMVar clientState
        return $ ChainSync.SendMsgFindIntersect
          (wrapLocalState cs)
          receiveRemoteState

      receiveRemoteState :: ChainSync.ClientStIntersect Block Tip IO ()
      receiveRemoteState =
        ChainSync.ClientStIntersect
        { ChainSync.recvMsgIntersectFound    = \point _ ->
            ChainSync.ChainSyncClient $ do
              runNodeClientEffects connection clientState $
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
              runNodeClientEffects connection clientState $
                publishNewBlock block
              return requestNext
        , ChainSync.recvMsgRollBackward = error "Not supported."
        }

txSubmissionClient :: Connection
                   -> MVar ClientState
                   -> TQueue Tx
                   -> TxSubmission.LocalTxSubmissionClient Tx String IO ()
txSubmissionClient connection clientState txInput =
    TxSubmission.LocalTxSubmissionClient pushTxs
    where
      pushTxs :: IO (TxSubmission.LocalTxClientStIdle Tx String IO ())
      pushTxs = do
        header <- atomically $ readTQueue txInput
        runNodeClientEffects connection clientState $
          sendTx header
        return $ TxSubmission.SendMsgSubmitTx
                   header
                   (const pushTxs) -- ignore rejects for now

-- Working with the log.
localStateProjection =
  Projection
    { projectionSeed = emptyClientState
    , projectionEventHandler = blockAddedHandler
    }
  where
    blockAddedHandler :: ClientState -> VersionedStreamEvent ChainEvent -> ClientState
    blockAddedHandler oldState
                      (StreamEvent _ _ (NodeEvent (BlockAdded block))) =
        over csIndex (Index.insertBlock block)
      $ over csChain (block :)
      $ over csCurrentSlot (+1) oldState
    blockAddedHandler oldState _ = oldState

localStateRefresh :: MonadIO m
                  => MonadEventStore ChainEvent m
                  => Second
                  -> MVar ClientState
                  -> m ()
localStateRefresh delay localState =
    go (globalStreamProjection localStateProjection)
  where
    go :: MonadIO m
       => MonadEventStore ChainEvent m
       => GlobalStreamProjection ClientState ChainEvent
       -> m ()
    go projection = do
        nextProjection <- refreshProjection projection
        liftIO $ do
          _ <- swapMVar localState (streamProjectionState nextProjection)
          threadDelay (fromIntegral $ toMicroseconds delay)
        go nextProjection

runNodeClientEffects ::
    Connection
 -> MVar ClientState
 -> Eff (NodeClientEffects IO) a
 -> IO (a, [Tx])
runNodeClientEffects = undefined

runEventStore :: Connection
                   -> ReaderT Connection (LoggingT IO) a
                   -> IO ()
runEventStore connection m =
    void
  $ runStdoutLoggingT
  $ runReaderT m connection
