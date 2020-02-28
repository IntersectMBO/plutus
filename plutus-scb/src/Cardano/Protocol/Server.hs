{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs             #-}
{-# LANGUAGE TypeFamilies      #-}
{-# LANGUAGE TypeOperators     #-}
module Cardano.Protocol.Server where

import qualified Data.ByteString.Lazy                                as LBS
import           Data.Functor.Contravariant                          (contramap)
import           Data.List                                           ((!!))
import           Data.Void                                           (Void)

import           Control.Concurrent
import           Control.Concurrent.Async
import           Control.Lens
import           Control.Tracer

import qualified Ouroboros.Network.Protocol.ChainSync.Server         as ChainSync
import qualified Ouroboros.Network.Protocol.LocalTxSubmission.Server as TxSubmission

import           Network.Mux.Types                                   (AppType (..))
import           Ouroboros.Network.Magic
import           Ouroboros.Network.Mux
import           Ouroboros.Network.NodeToNode
import           Ouroboros.Network.Protocol.Handshake.Type
import           Ouroboros.Network.Protocol.Handshake.Version
import           Ouroboros.Network.Socket

import           Codec.Serialise                                     (DeserialiseFailure)

import           Cardano.Protocol.Effects
import qualified Cardano.Protocol.Puppet.Server                      as Puppet
import           Cardano.Protocol.Type

import           Ledger                                              (Block, Tx (..))
import qualified Wallet.Emulator.Chain                               as EC

startServerNode :: FilePath -> ChainState -> IO Void
startServerNode sockAddr initialState = do
    networkState <- newNetworkMutableState
    _ <- async $ cleanNetworkMutableState networkState
    state <- newMVar initialState
    withServerNode
      nullNetworkServerTracers
      networkState
      (mkLocalSocketAddrInfo sockAddr)
      cborTermVersionDataCodec
      (\(DictVersion _) -> acceptEq)
      (simpleSingletonVersions (0 :: Int)
                               (NodeToNodeVersionData $ NetworkMagic 0)
                               (DictVersion nodeToNodeCodecCBORTerm) (app state))
      nullErrorPolicies
      $ \_ serverAsync ->
        wait serverAsync
    where
      app :: MVar ChainState
          -> OuroborosApplication 'ResponderApp
                                  ConnectionId
                                  NodeToClientPtcls
                                  IO LBS.ByteString Void ()
      app = simpleResponderApplication . protocols

      protocols :: MVar ChainState
                -> NodeToClientPtcls
                -> MuxPeer ConnectionId
                     DeserialiseFailure
                     IO LBS.ByteString ()
      protocols state ChainSyncWithBlocksPtcl =
          MuxPeer
            (contramap show stdoutTracer)
            codecChainSync
            (ChainSync.chainSyncServerPeer (chainSyncServer state))

      protocols state LocalTxSubmissionPtcl =
          MuxPeer
            (contramap show stdoutTracer)
            codecTxSubmission
            (TxSubmission.localTxSubmissionServerPeer (return (txSubmissionServer state)))

      protocols state PuppetPtcl =
          MuxPeer
            (contramap show stdoutTracer)
            codecPuppet
            (Puppet.puppetServerPeer (return (puppetServer state)))

puppetServer :: MVar ChainState
             -> Puppet.PuppetServer ChainState Block IO ()
puppetServer state = idleState
  where
    idleState =
      Puppet.PuppetServer {
        Puppet.recvMsgRequestState = do
          st <- readMVar state
          return (st, idleState)

      , Puppet.recvMsgValidate = do
          (_, block) <-
            wrapChainEffects state EC.processBlock
          return ( block , idleState )

      , Puppet.recvMsgDone = ()
      }

txSubmissionServer :: MVar ChainState
                   -> TxSubmission.LocalTxSubmissionServer Tx String IO ()
txSubmissionServer state = idleState
    where
      idleState :: TxSubmission.LocalTxSubmissionServer Tx String IO ()
      idleState =
        TxSubmission.LocalTxSubmissionServer {
          TxSubmission.recvMsgSubmitTx =
            \tx -> do
                st <- takeMVar state
                putMVar state (over txPool (tx :) st)
                return (Nothing, idleState)
        , TxSubmission.recvMsgDone     = ()
        }

chainSyncServer :: MVar ChainState
                -> ChainSync.ChainSyncServer Block Tip IO ()
chainSyncServer state =
    ChainSync.ChainSyncServer (idleState 0)
    where
      idleState :: Offset
                -> IO (ChainSync.ServerStIdle Block Tip IO ())
      idleState offset  = return $
        ChainSync.ServerStIdle {
          ChainSync.recvMsgRequestNext = nextState offset
        , ChainSync.recvMsgFindIntersect = \_ -> intersectState offset
        , ChainSync.recvMsgDoneClient = return ()
        }

      nextState :: Offset
                -> IO (Either (ChainSync.ServerStNext Block Tip IO ())
                              (IO (ChainSync.ServerStNext Block Tip IO ())))
      nextState offset = do
        st <- readMVar state
        return $ if offset `lowerThanSlot` st
                 then Right $ do
                                st' <- whileT (offset `lowerThanSlot`) state
                                return $ rollForward st' offset
                 else Left  $ rollForward st offset

      rollForward :: ChainState -> Int -> ChainSync.ServerStNext Block Tip IO ()
      rollForward st offset =
        ChainSync.SendMsgRollForward
          (reverse (snd <$> st ^. chainNewestFirst) !! offset)
          (head    (snd <$> st ^. chainNewestFirst))
          (ChainSync.ChainSyncServer (idleState (offset + 1)))

      lowerThanSlot :: Int -> ChainState -> Bool
      lowerThanSlot offset st =
        length (st ^. chainNewestFirst) <= offset

      intersectState :: Offset
                     -> IO (ChainSync.ServerStIntersect Block Tip IO ())
      intersectState _ = error "Not supported."

whileT :: (a -> Bool) -> MVar a -> IO a
whileT p ma = do
    a <- readMVar ma
    if p a
    then do
      threadDelay 500000
      whileT p ma
    else return a
