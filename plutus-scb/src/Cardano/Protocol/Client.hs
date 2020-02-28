{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE DeriveAnyClass    #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs             #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TypeFamilies      #-}
module Cardano.Protocol.Client where

import qualified Data.ByteString.Lazy                                as LBS
import           Data.Functor.Contravariant                          (contramap)
import qualified Data.Map.Lazy                                       as Map
import           Data.Void                                           (Void)

import           Control.Concurrent
import           Control.Concurrent.STM
import           Control.Lens
import           Control.Monad.Logger
import           Control.Monad.Reader
import           Control.Tracer

import           Eventful.Aggregate                                  (Aggregate (..))
import           Eventful.Projection                                 (Projection (..))
import           Eventful.Store.Class

import qualified Cardano.Protocol.Puppet.Client                      as Puppet
import qualified Ouroboros.Network.Protocol.ChainSync.Client         as ChainSync
import qualified Ouroboros.Network.Protocol.LocalTxSubmission.Client as TxSubmission

import           Cardano.Slotting.Slot                               (SlotNo (..))
import           Codec.Serialise                                     (DeserialiseFailure)
import           Network.Mux.Types                                   (AppType (..))
import           Ouroboros.Network.Magic
import           Ouroboros.Network.Mux
import           Ouroboros.Network.NodeToNode
import           Ouroboros.Network.Protocol.Handshake.Type
import           Ouroboros.Network.Protocol.Handshake.Version
import           Ouroboros.Network.Socket

import           Cardano.Protocol.Type

import           Ledger                                              (Block, Tx (..))
import qualified Ledger.Index                                        as Index
import           Plutus.SCB.Core
import           Plutus.SCB.Events
import           Plutus.SCB.Query                                    (nullProjection)

data ClientState = ClientState
  { _csChain :: [(SlotNo, Block)]
  , _csIndex :: Index.UtxoIndex
  } deriving Show

makeLenses ''ClientState

emptyClientState :: ClientState
emptyClientState = ClientState [] (Index.UtxoIndex Map.empty)

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
            (TxSubmission.localTxSubmissionClientPeer (txSubmissionClient connection (txInputQueue endpoint)))

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
chainSyncClient connection state =
    ChainSync.ChainSyncClient (return requestNext)
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
              st <- readMVar state
              void $ runMonadEventStore connection $
                runCommand logBlock NodeEventSource (block, st)
              return requestNext
        , ChainSync.recvMsgRollBackward = error "Not supported."
        }

txSubmissionClient :: Connection
                   -> TQueue Tx
                   -> TxSubmission.LocalTxSubmissionClient Tx String IO ()
txSubmissionClient connection txInput =
    TxSubmission.LocalTxSubmissionClient pushTxs
    where
      pushTxs :: IO (TxSubmission.LocalTxClientStIdle Tx String IO ())
      pushTxs = do
        header <- atomically $ readTQueue txInput
        void $ runMonadEventStore connection $
          runCommand logTx NodeEventSource header
        return $ TxSubmission.SendMsgSubmitTx
                   header
                   (const pushTxs) -- ignore rejects for now

-- Working with the log.
logBlock :: Aggregate () ChainEvent (Block, ClientState)
logBlock =
  Aggregate
    { aggregateProjection = nullProjection
    , aggregateCommandHandler =
        \() (block, state) ->
          [ NodeEvent $ BlockAdded block
          , NodeEvent $ NewSlot  (fromIntegral $ length (view csChain state)) [] ]
    }

logTx :: Aggregate () ChainEvent Tx
logTx =
  Aggregate
    { aggregateProjection = nullProjection
    , aggregateCommandHandler =
        \() tx ->
          [ NodeEvent $ SubmittedTx tx ]
    }

localClientState :: Projection ClientState (VersionedStreamEvent ChainEvent)
localClientState =
  Projection
    { projectionSeed = emptyClientState
    , projectionEventHandler = blockAddedHandler
    }
  where
    blockAddedHandler :: ClientState -> VersionedStreamEvent ChainEvent -> ClientState
    blockAddedHandler oldState@(ClientState ((slot, _) : _) _)
                      (StreamEvent _ _ (NodeEvent (BlockAdded block))) =
      over csIndex (Index.insertBlock block) $
      over csChain ((slot + 1, block) :) oldState
    blockAddedHandler oldState _ = oldState

runMonadEventStore :: Connection
                   -> ReaderT Connection (LoggingT IO) a
                   -> IO a
runMonadEventStore connection m =
  runStdoutLoggingT (runReaderT m connection)
