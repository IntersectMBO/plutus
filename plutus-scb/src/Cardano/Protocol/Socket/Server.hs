{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs             #-}
{-# LANGUAGE TypeFamilies      #-}
{-# LANGUAGE TypeOperators     #-}
module Cardano.Protocol.Socket.Server where

import qualified Data.ByteString.Lazy                                as LBS
import           Data.Functor.Contravariant                          (contramap)
import           Data.List                                           (intersect, (!!))
import           Data.Maybe                                          (listToMaybe)
import           Data.Void                                           (Void)

import           Control.Concurrent
import           Control.Concurrent.Async
import           Control.Lens
import           Control.Tracer

import qualified Ouroboros.Network.Protocol.ChainSync.Server         as ChainSync
import qualified Ouroboros.Network.Protocol.LocalTxSubmission.Server as TxSubmission

import           Network.Mux.Types                                   (AppType (..))
import           Ouroboros.Network.Block                             (Point (..))
import           Ouroboros.Network.Magic
import           Ouroboros.Network.Mux
import           Ouroboros.Network.NodeToNode
import           Ouroboros.Network.Protocol.Handshake.Type
import           Ouroboros.Network.Protocol.Handshake.Version
import           Ouroboros.Network.Socket

import           Codec.Serialise                                     (DeserialiseFailure)
import           Cardano.Protocol.Socket.Type
import           Cardano.Protocol
import           Ledger                                              (Block, Tx (..))
import           Wallet.Emulator.Chain

startServerNode :: FilePath -> MVar ChainState -> IO Void
startServerNode sockAddr stateVar = do
    networkState <- newNetworkMutableState
    _ <- async $ cleanNetworkMutableState networkState
    withServerNode
      nullNetworkServerTracers
      networkState
      (mkLocalSocketAddrInfo sockAddr)
      cborTermVersionDataCodec
      (\(DictVersion _) -> acceptEq)
      (simpleSingletonVersions (0 :: Int)
                               (NodeToNodeVersionData $ NetworkMagic 0)
                               (DictVersion nodeToNodeCodecCBORTerm) (app stateVar))
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

      protocols state LocalTxSubmissionPtcl =
          MuxPeer
            (contramap show stdoutTracer)
            codecTxSubmission
            (TxSubmission.localTxSubmissionServerPeer (return (txSubmissionServer state)))

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
        , ChainSync.recvMsgFindIntersect = \pts -> do
                st <- readMVar state
                return $ intersectState st pts
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
          (reverse (st ^. chainNewestFirst) !! offset)
          (head    (st ^. chainNewestFirst))
          (ChainSync.ChainSyncServer (idleState (offset + 1)))

      lowerThanSlot :: Int -> ChainState -> Bool
      lowerThanSlot offset st =
        length (st ^. chainNewestFirst) <= offset

      intersectState :: ChainState
                     -> [Point Block]
                     -> ChainSync.ServerStIntersect Block Tip IO ()
      intersectState st clientPts =
        let pt = listToMaybe $ intersect
                   (getChainPoints st)
                   clientPts
        in case pt of
             Nothing ->
               ChainSync.SendMsgIntersectNotFound
                 (head $ view chainNewestFirst st)
                 -- No intersection found. Resume from begining.
                 (ChainSync.ChainSyncServer $ idleState 0)
             Just pt' ->
               ChainSync.SendMsgIntersectFound
                 pt'
                 (head $ view chainNewestFirst st)
                 (ChainSync.ChainSyncServer $ idleState $ pointOffset pt')

whileT :: (a -> Bool) -> MVar a -> IO a
whileT p ma = do
    a <- readMVar ma
    if p a
    then do
      threadDelay 500000
      whileT p ma
    else return a
