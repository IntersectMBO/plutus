{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs             #-}
{-# LANGUAGE TypeFamilies      #-}
{-# LANGUAGE TypeOperators     #-}
module Cardano.Protocol.Socket.Server where

import qualified Data.ByteString.Lazy                                as LBS
import           Data.List                                           (intersect)
import           Data.Maybe                                          (listToMaybe)
import           Data.Void                                           (Void)

import           Control.Concurrent
import           Control.Concurrent.Async
import           Control.Lens
import           Control.Tracer

import qualified Ouroboros.Network.Protocol.ChainSync.Server         as ChainSync
import qualified Ouroboros.Network.Protocol.LocalTxSubmission.Server as TxSubmission

import           Cardano.Slotting.Slot                               (SlotNo (..), WithOrigin (..))
import           Ouroboros.Network.Block                             (Point (..), pointSlot)
import           Ouroboros.Network.IOManager
import           Ouroboros.Network.Magic
import           Ouroboros.Network.Mux
import           Ouroboros.Network.NodeToNode
import qualified Ouroboros.Network.Point                             as OP (Block (..))
import           Ouroboros.Network.Protocol.Handshake.Type
import           Ouroboros.Network.Protocol.Handshake.Unversioned
import           Ouroboros.Network.Protocol.Handshake.Version
import           Ouroboros.Network.Socket
import           Ouroboros.Network.Snocket

import           Cardano.Protocol.Socket.Type

import           Ledger                                              (Block, Slot (..), Tx (..))
import           Wallet.Emulator.Chain

-- mv ChainState AppState
startServerNode :: FilePath -> ChainState -> IO Void
startServerNode sockAddr initialState = withIOManager $ \iocp -> do
    networkState <- newNetworkMutableState
    _ <- async $ cleanNetworkMutableState networkState
    stateMV <- newMVar initialState
    withServerNode
      (localSnocket iocp "")
      nullNetworkServerTracers
      networkState
      (AcceptedConnectionsLimit maxBound maxBound 0)
      (localAddressFromPath sockAddr)
      unversionedHandshakeCodec
      cborTermVersionDataCodec
      (\(DictVersion _) -> acceptableVersion)
      (simpleSingletonVersions UnversionedProtocol
                               (NodeToNodeVersionData $ NetworkMagic 0)
                               (DictVersion nodeToNodeCodecCBORTerm)
                               (\_peerid -> SomeResponderApplication (app stateMV)))
      nullErrorPolicies
      $ \_ serverAsync ->
        wait serverAsync
    where
      app :: MVar ChainState
          -> OuroborosApplication 'ResponderApp
                                  LBS.ByteString
                                  IO Void ()
      app stateMV = nodeApplication (chainSync stateMV) (txSubmission stateMV)

      chainSync :: MVar ChainState
                -> RunMiniProtocol 'ResponderApp LBS.ByteString IO Void ()
      chainSync stateMV =
          ResponderProtocolOnly $
          MuxPeer
            (contramap show stdoutTracer)
            codecChainSync
            (ChainSync.chainSyncServerPeer (chainSyncServer stateMV))

      txSubmission :: MVar ChainState
                   -> RunMiniProtocol 'ResponderApp LBS.ByteString IO Void ()
      txSubmission stateMV =
          ResponderProtocolOnly $
          MuxPeer
            (contramap show stdoutTracer)
            codecTxSubmission
            (TxSubmission.localTxSubmissionServerPeer (pure $ txSubmissionServer stateMV))

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
        -- TODO: Can use slot numbers to make it more efficient
        let pt = listToMaybe $ intersect
                   (getChainPoints st)
                   clientPts
        in case pt of
             Nothing ->
               ChainSync.SendMsgIntersectNotFound
                 (head $ view chainNewestFirst st)
                 -- No intersection found. Resume from origin.
                 (ChainSync.ChainSyncServer $ idleState 0)
             Just pt' ->
               ChainSync.SendMsgIntersectFound
                 pt'
                 (head $ view chainNewestFirst st)
                 (ChainSync.ChainSyncServer $ idleState $ pointOffset pt')

pointOffset :: Point Block
            -> Int
pointOffset pt =
  case pointSlot pt of
    Origin        -> 0
    At (SlotNo s) -> fromIntegral s

getChainPoints :: ChainState -> [Point Block]
getChainPoints st =
  zipWith mkPoint
    [(st ^. currentSlot) .. 0]
    (st ^. chainNewestFirst)
  where
    mkPoint :: Slot -> Block -> Point Block
    mkPoint (Slot s) block =
      Point (At (OP.Block (SlotNo $ fromIntegral s)
                          (blockId block)))

whileT :: (a -> Bool) -> MVar a -> IO a
whileT p ma = do
    a <- readMVar ma
    if p a
    then do
      threadDelay 500000
      whileT p ma
    else return a
