{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE DeriveAnyClass    #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs             #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TypeFamilies      #-}
module Cardano.Protocol.Node where

import qualified Data.ByteString.Lazy                                as LBS
import           Data.Functor.Contravariant                          (contramap)
import           Data.List                                           ((!!))
import           Data.Void                                           (Void)
import           GHC.Generics

import           Control.Concurrent
import           Control.Concurrent.Async
import           Control.Concurrent.STM
import           Control.Lens
import           Control.Lens.Operators
import           Control.Tracer

import qualified Codec.CBOR.Decoding                                 as CBOR
import qualified Codec.CBOR.Encoding                                 as CBOR
import qualified Codec.CBOR.Read                                     as CBOR

import qualified Network.Socket                                      as Socket

import qualified Ouroboros.Network.Protocol.ChainSync.Client         as ChainSync
import qualified Ouroboros.Network.Protocol.ChainSync.Codec          as ChainSync
import qualified Ouroboros.Network.Protocol.ChainSync.Server         as ChainSync
import qualified Ouroboros.Network.Protocol.ChainSync.Type           as ChainSync

import qualified Ouroboros.Network.Protocol.LocalTxSubmission.Client as TxSubmission
import qualified Ouroboros.Network.Protocol.LocalTxSubmission.Codec  as TxSubmission
import qualified Ouroboros.Network.Protocol.LocalTxSubmission.Server as TxSubmission
import qualified Ouroboros.Network.Protocol.LocalTxSubmission.Type   as TxSubmission

import qualified Cardano.Protocol.Puppet.Client                              as Puppet
import qualified Cardano.Protocol.Puppet.Codec                               as Puppet
import qualified Cardano.Protocol.Puppet.Server                              as Puppet
import qualified Cardano.Protocol.Puppet.Type                                as Puppet

import           Ouroboros.Network.Block                             (HeaderHash, StandardHash)
import           Ouroboros.Network.Magic
import           Ouroboros.Network.Mux
import           Ouroboros.Network.NodeToNode
import           Ouroboros.Network.Protocol.Handshake.Type
import           Ouroboros.Network.Protocol.Handshake.Version
import           Ouroboros.Network.Socket

import           Codec.Serialise                                     (DeserialiseFailure)
import qualified Codec.Serialise                                     as CBOR

import           Network.Mux.Types                                   (AppType (..))
import           Network.TypedProtocol.Codec

import           Debug.Trace

import Cardano.Protocol.Type

startClientNode :: FilePath -> PuppetHandle -> IO ()
startClientNode sockAddr endpoint =
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
            (ChainSync.chainSyncClientPeer (chainSyncClient (txOutputQueue endpoint)))

      protocols LocalTxSubmissionPtcl =
          MuxPeer
            (contramap show stdoutTracer)
            codecTxSubmission
            (TxSubmission.localTxSubmissionClientPeer (txSubmissionClient (txInputQueue endpoint)))

      protocols PuppetPtcl =
          MuxPeer
            (contramap show stdoutTracer)
            codecPuppet
            (Puppet.puppetClientPeer (puppetClient (ctlRequest endpoint) (ctlResponse endpoint)))

puppetClient :: TQueue PuppetRequest
             -> TQueue PuppetResponse
             -> Puppet.PuppetClient ServerState Block IO ()
puppetClient req res =
    Puppet.PuppetClient processNextRequest
  where
    processNextRequest :: IO (Puppet.PuppetClientStIdle ServerState Block IO ())
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

chainSyncClient :: TQueue Block
                -> ChainSync.ChainSyncClient Block Tip IO ()
chainSyncClient txOutQ =
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
          ChainSync.recvMsgRollForward  = \header _ ->
            ChainSync.ChainSyncClient $ do
              addBlock header
              return requestNext
        , ChainSync.recvMsgRollBackward = error "Not supported."
        }

      addBlock :: Block -> IO ()
      addBlock block =
        atomically (writeTQueue txOutQ block)

txSubmissionClient :: TQueue Tx
                   -> TxSubmission.LocalTxSubmissionClient Tx String IO ()
txSubmissionClient txInput =
    TxSubmission.LocalTxSubmissionClient pushTxs
    where
      pushTxs :: IO (TxSubmission.LocalTxClientStIdle Tx String IO ())
      pushTxs = do
        header <- atomically $ readTQueue txInput
        return $ TxSubmission.SendMsgSubmitTx
                   header
                   (const pushTxs) -- ignore rejects for now
