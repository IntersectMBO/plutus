{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs             #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE NamedFieldPuns    #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}
{-# LANGUAGE TypeFamilies      #-}

module Cardano.Protocol.Socket.Server where

import qualified Data.ByteString.Lazy                                as LBS
import           Data.Foldable                                       (traverse_)
import           Data.List                                           (intersect)
import           Data.Maybe                                          (listToMaybe)
import           Data.Text                                           (Text)
import           Data.Void                                           (Void)

import           Control.Concurrent
import           Control.Concurrent.Async
import           Control.Concurrent.STM
import           Control.Lens                                        hiding (ix)
import           Control.Monad.Freer                                 (interpret, run)
import qualified Control.Monad.Freer.Extras.Log                      as Log
import           Control.Monad.Freer.State                           (runState)
import           Control.Monad.Reader
import           Control.Tracer

import           Ouroboros.Network.Protocol.ChainSync.Server         (ChainSyncServer (..), ServerStIdle (..),
                                                                      ServerStIntersect (..), ServerStNext (..))
import qualified Ouroboros.Network.Protocol.ChainSync.Server         as ChainSync
import qualified Ouroboros.Network.Protocol.LocalTxSubmission.Server as TxSubmission
import qualified Ouroboros.Network.Protocol.LocalTxSubmission.Type   as TxSubmission

import           Cardano.Slotting.Slot                               (SlotNo (..), WithOrigin (..))
import           Ouroboros.Network.Block                             (Point (..), pointSlot)
import           Ouroboros.Network.IOManager
import           Ouroboros.Network.Mux
import           Ouroboros.Network.NodeToNode
import qualified Ouroboros.Network.Point                             as OP (Block (..))
import           Ouroboros.Network.Protocol.Handshake.Codec
import           Ouroboros.Network.Protocol.Handshake.Unversioned
import           Ouroboros.Network.Protocol.Handshake.Version
import           Ouroboros.Network.Snocket
import           Ouroboros.Network.Socket

import           Cardano.Protocol.Socket.Type

import           Ledger                                              (Block, Slot (..), Tx (..))
import           Wallet.Emulator.Chain                               (ChainState (..))
import qualified Wallet.Emulator.Chain                               as Chain

import qualified Debug.Trace                                         as Dbg

data CommandChannel = CommandChannel
  { ccCommand  :: TQueue ServerCommand
  , ccResponse :: TQueue ServerResponse
  }

type Error a = Either Text a

{- | Clone the original channel for each connected client, then use
     this wrapper to make sure that no data is consumed from the
     original channel. -}
newtype LocalChannel = LocalChannel (TChan Block)

{- | A handler used to pass around the path to the server
     and channels used for controlling the server. -}
data ServerHandler = ServerHandler {
    shSocketPath     :: FilePath,
    -- The client will send a `ServerCommand` and the server will
    -- respond with a `ServerResponse`.
    shCommandChannel :: CommandChannel
}

{- | The commands that control the server. This API is not part of the client
     interface, and in order to call them directly you will need access to the
     returned ServerHandler -}
data ServerCommand =
    -- This command will add a new block by processing
    -- transactions in the memory pool.
    ProcessBlock
    -- Append a transaction to the transaction pool.
  | AddTx Tx
    -- Trim the blockchain to the size given by the argument
  | TrimTo Int
    deriving Show

{- | The response from the server. Can be used for the information
     passed back, or for synchronisation.
-}
data ServerResponse =
    -- A block was added. We are using this for synchronization.
    BlockAdded Block
    deriving Show

processBlock :: MonadIO m => ServerHandler -> m Block
processBlock ServerHandler {shCommandChannel} = do
    liftIO $ atomically $ writeTQueue (ccCommand shCommandChannel) $ ProcessBlock
    -- Wait for the server to finish processing blocks.
    liftIO $ atomically $ readTQueue (ccResponse shCommandChannel) >>= \case
        BlockAdded block -> pure block

addTx :: MonadIO m => ServerHandler -> Tx -> m ()
addTx ServerHandler { shCommandChannel } tx = do
    liftIO $ atomically $ writeTQueue (ccCommand  shCommandChannel) $ AddTx tx

trimTo :: MonadIO m => ServerHandler -> Int -> m ()
trimTo ServerHandler {shCommandChannel} size =
    liftIO $ atomically $ writeTQueue (ccCommand shCommandChannel) $ TrimTo size

handleCommand ::
    MonadIO m
 => CommandChannel
 -> InternalState
 -> m ()
handleCommand CommandChannel {ccCommand, ccResponse}
              InternalState  {isBlocks , isState   } =
    liftIO (atomically $ readTQueue ccCommand) >>= \case
        AddTx tx     ->
            liftIO $ modifyMVar_ isState (pure . over Chain.txPool (tx :))
        ProcessBlock -> liftIO $ do
            state <- liftIO $ takeMVar isState
            let (block, nextState') = Chain.processBlock
                  & interpret Chain.handleControlChain
                  & Log.handleLogIgnore @Chain.ChainEvent
                  & runState state
                  & run
            putMVar isState nextState'
            atomically $ do
                writeTChan  isBlocks   block
                writeTQueue ccResponse (BlockAdded block)
        TrimTo size ->
            liftIO $ modifyMVar_ isState (pure . over Chain.chainNewestFirst (take size))

{- | Start the server in a new thread, and return a server handler
     used to control the server -}
runServerNode ::
    MonadIO m
 => FilePath
 -> ChainState
 -> m ServerHandler
runServerNode shSocketPath initialState = liftIO $ do
    serverState      <- Dbg.trace "[xxx] running server node" $ initialiseInternalState initialState
    shCommandChannel <- CommandChannel <$> newTQueueIO <*> newTQueueIO
    void $ forkIO . void    $ protocolLoop  shSocketPath     serverState
    void $ forkIO . forever $ handleCommand shCommandChannel serverState
    pure $ ServerHandler { shSocketPath, shCommandChannel }

-- * Internal state

{- Store a channel (that is *never* cleared, for now) containing all
   the blocks, and the state required for validating the next block. -}
data InternalState = InternalState {
    isBlocks :: TChan Block,      -- ^ Broadcast channel for the whole chain.
    isState  :: MVar ChainState   -- ^ Used to track the tip of the chain.
}

initialiseInternalState ::
    MonadIO m
 => ChainState
 -> m InternalState
initialiseInternalState chainState = liftIO $ do
    isBlocks <- newTChanIO
    isState  <- newMVar chainState
    traverse_ (atomically . writeTChan isBlocks)
              (view Chain.chainNewestFirst chainState)
    pure InternalState { isBlocks, isState }

-- * ChainSync protocol

{- A monad for running all code executed when a state
   transition is invoked. It makes the implementation of
   state transitions easier to read. -}

type ChainSyncMonad = ReaderT InternalState IO

runChainSync :: InternalState -> ChainSyncMonad a -> IO a
runChainSync = flip runReaderT

{- The initial state of the protocol. You can move into
   requesting the next block or reset state by searching for an
   intersection. -}
idleState ::
    ( MonadReader InternalState m
    , MonadIO m )
 => Maybe LocalChannel
 -> m (ServerStIdle Block (Point Block) Tip m ())
idleState (Just channel) =
    pure ServerStIdle {
        recvMsgRequestNext = nextState channel,
        recvMsgFindIntersect = findIntersect,
        recvMsgDoneClient = return ()
    }
idleState Nothing = undefined

{- Get the next block, either immediately (the Just/Left branch)
   or within a monad (IO, in our case) where you can wait for the
   next block (Nothing/Right branch) -}
nextState ::
    ( MonadReader InternalState m
    , MonadIO m )
 => LocalChannel
 -> m (Either (ServerStNext Block (Point Block) Tip m ())
              (m (ServerStNext Block (Point Block) Tip m ())))
nextState localChannel@(LocalChannel channel) = do
    chainState <- ask <&> isState
    tip <- head . view Chain.chainNewestFirst <$>
           liftIO (readMVar chainState)
    (liftIO . atomically $ tryReadTChan channel) >>= \case
        Nothing -> Right . pure <$> do
            nextBlock <- liftIO . atomically $ readTChan channel
            sendRollForward localChannel tip nextBlock
        Just nextBlock -> Left  <$>
            sendRollForward localChannel tip nextBlock

{- This protocol state will search for a block intersection
   with some client provided blocks. When an intersection is found
   the client state is reset to the new offset (the Just branch)
   or to the genesis block if no intersection was found. -}
findIntersect ::
    ( MonadReader InternalState m
    , MonadIO m )
 => [Point Block]
 -> m (ServerStIntersect Block (Point Block) Tip m ())
findIntersect clientPoints = do
    chainState <- ask <&> isState >>= liftIO . readMVar
    let point = listToMaybe
              $ intersect (getChainPoints chainState)
                          clientPoints
    pure $ case point of
        Nothing ->
          SendMsgIntersectNotFound
            (head $ view Chain.chainNewestFirst chainState)
            -- No intersection found. Resume from origin.
            (ChainSyncServer $ cloneChainFrom 0 >>= idleState)
        Just point' ->
          SendMsgIntersectFound
            point'
            (head $ view Chain.chainNewestFirst chainState)
            -- Resuming from point'.
            (ChainSyncServer $ cloneChainFrom (pointOffset point') >>= idleState)

{- This is a wrapper around the creation of a `ServerStNext` -}
sendRollForward ::
    ( MonadReader InternalState m
    , MonadIO m )
 => LocalChannel
 -> Block -- tip
 -> Block -- current
 -> m (ServerStNext Block (Point Block) Tip m ())
sendRollForward channel tip current = pure $
    SendMsgRollForward
        current
        tip
        (ChainSyncServer (idleState (Just channel)))

{- This is the state for a new connection. For now we start with
   slot 0, and in idleState. This will probably change, since it
   makes more sense to start in the `StIntersect` state. -}
chainSyncServer ::
    ( MonadReader InternalState m
    , MonadIO m )
 => ChainSyncServer Block (Point Block) Tip m ()
chainSyncServer =
    ChainSyncServer (cloneChainFrom 0 >>= idleState)

{- Use a `TChan` to model a broadcast channel of which we
   clone (with potentially varying offsets) for clients. -}
cloneChainFrom :: forall m.
    ( MonadReader InternalState m
    , MonadIO m )
 => Integer
 -> m (Maybe LocalChannel)
cloneChainFrom offset = (LocalChannel <$>) <$> go
  where
    go :: m (Maybe (TChan Block))
    go = do
        blocks <- ask <&> isBlocks
        liftIO $ atomically $ do
            newChannel <- cloneTChan blocks
            consume newChannel offset

    consume :: TChan a -> Integer -> STM (Maybe (TChan a))
    consume channel' ix | ix == 0    = pure $ Just channel'
    consume channel' ix =
        -- We should have all requested blocks available on the
        -- channel, for consumption.
        tryReadTChan channel' >> consume channel' (ix - 1)

-- * Protocol setup

{- The node protocols always run in the IO monad. I wanted to use a
   different monad stack (mainly to be able to pass the internal state
   in a `MonadReader` and future proofing) so I wrote some hoisting
   functions for each of the states which transform the `ChainSyncMonad`
   into IO. -}

hoistChainSync ::
    MonadReader InternalState m
 => ChainSyncServer Block (Point Block) Tip ChainSyncMonad a
 -> m (ChainSyncServer Block (Point Block) Tip IO a)
hoistChainSync machine = do
    internalState <- ask
    pure ChainSyncServer {
        {- The basic idea is running the reader monad to remove it,
           leaving only IO, which is what we need. We do the same for all
           other states. -}
        runChainSyncServer = runChainSync internalState $
            runChainSyncServer machine >>= hoistStIdle
    }

hoistStIdle ::
    MonadReader InternalState m
 => ServerStIdle Block (Point Block) Tip ChainSyncMonad a
 -> m (ServerStIdle Block (Point Block) Tip IO a)
hoistStIdle (ServerStIdle nextState' findIntersect' done) = do
    internalState <- ask
    pure ServerStIdle {
        recvMsgRequestNext =
            runChainSync internalState $
                nextState' >>= \case
                    Left stNext -> Left         <$>  hoistStNext     stNext
                    Right mNext -> Right . pure <$> (hoistStNext =<< mNext ),
        recvMsgFindIntersect = \points ->
            runChainSync internalState
                         (findIntersect' points >>= hoistStIntersect),
        recvMsgDoneClient    = runChainSync internalState done
   }

hoistStIntersect ::
    MonadReader InternalState m
 => ServerStIntersect Block (Point Block) Tip ChainSyncMonad a
 -> m (ServerStIntersect Block (Point Block) Tip IO a)
hoistStIntersect (SendMsgIntersectFound point tip nextState') =
    SendMsgIntersectFound point tip <$> hoistChainSync nextState'
hoistStIntersect (SendMsgIntersectNotFound tip nextState') =
    SendMsgIntersectNotFound tip    <$> hoistChainSync nextState'

hoistStNext ::
    MonadReader InternalState m
 => ServerStNext Block (Point Block) Tip ChainSyncMonad a
 -> m (ServerStNext Block (Point Block) Tip IO a)
hoistStNext (SendMsgRollForward header tip nextState') =
    SendMsgRollForward header tip <$> hoistChainSync nextState'
hoistStNext (SendMsgRollBackward header tip nextState') =
    SendMsgRollBackward header tip <$> hoistChainSync nextState'

{- This is boilerplate code that sets up the node protocols,
   you can find in:
     ouroboros-network/ouroboros-network/demo/chain-sync.hs -}

protocolLoop ::
    MonadIO m
 => FilePath
 -> InternalState
 -> m Void
protocolLoop socketPath internalState = liftIO $ withIOManager $ \iocp -> do
    networkState <- newNetworkMutableState
    _ <- async $ cleanNetworkMutableState networkState
    withServerNode
      (localSnocket iocp "")
      nullNetworkServerTracers
      networkState
      (AcceptedConnectionsLimit maxBound maxBound 0)
      (localAddressFromPath socketPath)
      unversionedHandshakeCodec
      (cborTermVersionDataCodec unversionedProtocolDataCodec)
      acceptableVersion
      (unversionedProtocol (SomeResponderApplication (application internalState)))
      nullErrorPolicies
      $ \_ serverAsync -> wait serverAsync

application ::
    InternalState
 -> OuroborosApplication 'ResponderMode
                         addr
                         LBS.ByteString
                         IO Void ()
application internalState@InternalState {isState} =
    nodeApplication chainSync txSubmission
    where
        chainSync :: RunMiniProtocol 'ResponderMode LBS.ByteString IO Void ()
        chainSync =
             ResponderProtocolOnly $
             MuxPeer
               (contramap show stdoutTracer)
               codecChainSync
               (ChainSync.chainSyncServerPeer
                   (runReader (hoistChainSync chainSyncServer)
                              internalState))

        txSubmission :: RunMiniProtocol 'ResponderMode LBS.ByteString IO Void ()
        txSubmission =
            ResponderProtocolOnly $
            MuxPeer
              (contramap show stdoutTracer)
              codecTxSubmission
              (TxSubmission.localTxSubmissionServerPeer (pure $ txSubmissionServer isState))

-- * Computing intersections

-- Given a `Point` find its offset into the chain.
pointOffset :: Point Block
            -> Integer
pointOffset pt =
  case pointSlot pt of
    Origin        -> 0
    At (SlotNo s) -> fromIntegral s

-- Currently selects all points from the blockchain.
getChainPoints :: ChainState -> [Point Block]
getChainPoints st =
  zipWith mkPoint
    [(st ^. Chain.currentSlot) .. 0]
    (st ^. Chain.chainNewestFirst)
  where
    mkPoint :: Slot -> Block -> Point Block
    mkPoint (Slot s) block =
      Point (At (OP.Block (SlotNo $ fromIntegral s)
                          (blockId block)))

-- * TxSubmission protocol

{- I did not use the same approach for this protocol as I did
   for the `ChainSync`. This protocol has only one state and
   it is much simpler. -}

txSubmissionServer ::
    MVar ChainState
 -> TxSubmission.LocalTxSubmissionServer Tx String IO ()
txSubmissionServer state = txSubmissionState
    where
      txSubmissionState :: TxSubmission.LocalTxSubmissionServer Tx String IO ()
      txSubmissionState =
        TxSubmission.LocalTxSubmissionServer {
          TxSubmission.recvMsgSubmitTx =
            \tx -> do
                modifyMVar_ state (pure . over Chain.txPool (Chain.addTxToPool tx))
                return (TxSubmission.SubmitSuccess, txSubmissionState)
        , TxSubmission.recvMsgDone     = ()
        }
