{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs             #-}
{-# LANGUAGE TypeFamilies      #-}
{-# LANGUAGE TypeOperators     #-}
module Cardano.Protocol.Socket.Server where

import qualified Data.ByteString.Lazy                                as LBS
import           Data.List                                           (intersect)
import           Data.Maybe                                          (listToMaybe)
import           Data.Time.Units
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
import           Ouroboros.Network.Snocket
import           Ouroboros.Network.Socket

import           Cardano.Node.Types                                  (AppState (..), chainState)
import           Cardano.Protocol.Socket.Type

import           Ledger                                              (Block, Slot (..), Tx (..))
import           Wallet.Emulator.Chain

{-| This function starts a blockchain simulator as seen through a
    Cardano node.

    It received the path to the communication socket, and the server
    application state, then waits for requests using the `ChainSync`
    and `LocalTxSubmission` protocols.

    This follows the general pattern found in:
      ouroboros-network/demo/chain-sync.hs
-}
startServerNode :: FilePath -> MVar AppState -> IO Void
startServerNode sockPath stateMV = withIOManager $ \iocp -> do
    networkState <- newNetworkMutableState
    _ <- async $ cleanNetworkMutableState networkState
    withServerNode
      (localSnocket iocp "")
      nullNetworkServerTracers
      networkState
      (AcceptedConnectionsLimit maxBound maxBound 0)
      (localAddressFromPath sockPath)
      unversionedHandshakeCodec
      cborTermVersionDataCodec
      (\(DictVersion _) -> acceptableVersion)
      (simpleSingletonVersions UnversionedProtocol
                               (NodeToNodeVersionData $ NetworkMagic 0)
                               (DictVersion nodeToNodeCodecCBORTerm)
                               (\_peerid -> SomeResponderApplication app))
      nullErrorPolicies
      $ \_ serverAsync -> wait serverAsync

    where
      {- Application that communicates using 2 multiplexed protocols
         (ChainSync and TxSubmission, with BlockFetch coming soon). -}
      app :: OuroborosApplication 'ResponderApp
                                  LBS.ByteString
                                  IO Void ()
      app = nodeApplication chainSync txSubmission

      chainSync :: RunMiniProtocol 'ResponderApp LBS.ByteString IO Void ()
      chainSync =
          ResponderProtocolOnly $
          MuxPeer
            (contramap show stdoutTracer)
            codecChainSync
            (ChainSync.chainSyncServerPeer (chainSyncServer stateMV))

      txSubmission :: RunMiniProtocol 'ResponderApp LBS.ByteString IO Void ()
      txSubmission =
          ResponderProtocolOnly $
          MuxPeer
            (contramap show stdoutTracer)
            codecTxSubmission
            (TxSubmission.localTxSubmissionServerPeer (pure $ txSubmissionServer stateMV))

-- | The client updates the application state when the protocol state changes.
txSubmissionServer :: MVar AppState
                   -> TxSubmission.LocalTxSubmissionServer Tx String IO ()
txSubmissionServer state = idleState
    where
      idleState :: TxSubmission.LocalTxSubmissionServer Tx String IO ()
      idleState =
        TxSubmission.LocalTxSubmissionServer {
          TxSubmission.recvMsgSubmitTx =
            \tx -> do
                modifyMVar_ state (pure . over (chainState . txPool) (addTxToPool tx))
                return (Nothing, idleState)
        , TxSubmission.recvMsgDone     = ()
        }

-- | The server updates the application state when the protocol state changes.
chainSyncServer :: MVar AppState
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
                st <- view chainState <$> readMVar state
                return $ intersectState st pts
        , ChainSync.recvMsgDoneClient = return ()
        }

      {- If there is any available data, send it right away, otherwise wait until
         some new block is pushed. -}
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

      -- Send the new block to the client.
      rollForward :: AppState -> Integer -> ChainSync.ServerStNext Block Tip IO ()
      rollForward st offset =
        ChainSync.SendMsgRollForward
          (reverse (st ^. (chainState . chainNewestFirst)) !! (fromIntegral offset))
          (head    (st ^. (chainState . chainNewestFirst)))
          (ChainSync.ChainSyncServer (idleState (offset + 1)))

      -- Predicate that selects the slots that have not been seen at the given offset.
      lowerThanSlot :: Integer -> AppState -> Bool
      lowerThanSlot offset st =
        length (st ^. chainState . chainNewestFirst) <= (fromIntegral offset)

      {- Intersect client provided state with the server state and find the
         best slot to start streaming from. -}
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
                 -- No intersection found. Resume from origin.
                 (ChainSync.ChainSyncServer $ idleState 0)
             Just pt' ->
               ChainSync.SendMsgIntersectFound
                 pt'
                 (head $ view chainNewestFirst st)
                 (ChainSync.ChainSyncServer $ idleState $ pointOffset pt')

-- | Given a `Point` find its offset into the chain.
pointOffset :: Point Block
            -> Integer
pointOffset pt =
  case pointSlot pt of
    Origin        -> 0
    At (SlotNo s) -> fromIntegral s

-- | Currently selects all points from the blockchain.
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

{- | Wait until a predicate validates the shared data. Used to select
     the server state if there are new blocks available. -}
whileT :: (a -> Bool) -> MVar a -> IO a
whileT p ma = do
    a <- readMVar ma
    if p a
    then do
      let delay = 500 :: Millisecond
      threadDelay (fromIntegral $ toMicroseconds delay)
      whileT p ma
    else return a
