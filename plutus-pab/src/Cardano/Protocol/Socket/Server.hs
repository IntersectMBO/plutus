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

import           Cardano.BM.Data.Trace                               (Trace)
import           Cardano.Node.Types                                  (MockServerLogMsg (..))
import qualified Data.ByteString.Lazy                                as LBS
import           Data.List                                           (intersect)
import           Data.Maybe                                          (listToMaybe)
import           Data.Text                                           (Text)
import           Data.Void                                           (Void)

import           Control.Concurrent
import           Control.Concurrent.Async
import           Control.Concurrent.STM
import           Control.Lens                                        hiding (index, ix)
import           Control.Monad.Freer                                 (interpret, runM)
import           Control.Monad.Freer.State                           (runState)
import           Control.Monad.Reader
import           Control.Tracer

import           Ouroboros.Network.Protocol.ChainSync.Server         (ChainSyncServer (..), ServerStIdle (..),
                                                                      ServerStIntersect (..), ServerStNext (..))
import qualified Ouroboros.Network.Protocol.ChainSync.Server         as ChainSync
import qualified Ouroboros.Network.Protocol.LocalTxSubmission.Server as TxSubmission
import qualified Ouroboros.Network.Protocol.LocalTxSubmission.Type   as TxSubmission
import qualified Plutus.PAB.Monitoring.Util                          as LM

import           Cardano.Slotting.Slot                               (SlotNo (..), WithOrigin (..))
import           Ouroboros.Network.Block                             (Point (..), pointSlot)
import           Ouroboros.Network.IOManager
import           Ouroboros.Network.Mux
import           Ouroboros.Network.NodeToNode                        hiding (chainSyncMiniProtocolNum,
                                                                      txSubmissionMiniProtocolNum)
import qualified Ouroboros.Network.Point                             as OP (Block (..))
import           Ouroboros.Network.Protocol.Handshake.Codec
import           Ouroboros.Network.Protocol.Handshake.Unversioned
import           Ouroboros.Network.Protocol.Handshake.Version
import           Ouroboros.Network.Snocket
import           Ouroboros.Network.Socket

import           Cardano.Protocol.Socket.Type                        hiding (currentSlot)

import           Cardano.Chain                                       (MockNodeServerChainState (..), addTxToPool,
                                                                      chainNewestFirst, channel, currentSlot,
                                                                      getChannel, getTip, handleControlChain, tip,
                                                                      txPool)
import           Ledger                                              (Block, Slot (..), Tx (..))
import qualified Wallet.Emulator.Chain                               as Chain

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
    -- Set the slot number
  | ModifySlot (Slot -> Slot)
    -- Append a transaction to the transaction pool.
  | AddTx Tx

instance Show ServerCommand where
    show = \case
        ProcessBlock -> "ProcessBlock"
        ModifySlot _ -> "ModifySlot"
        AddTx t      -> "AddTx " <> show t

{- | The response from the server. Can be used for the information
     passed back, or for synchronisation.
-}
data ServerResponse =
    -- A block was added. We are using this for synchronization.
    BlockAdded Block
    | SlotChanged Slot
    deriving Show

processBlock :: MonadIO m => ServerHandler -> m Block
processBlock ServerHandler {shCommandChannel} = do
    liftIO $ atomically $ writeTQueue (ccCommand shCommandChannel) ProcessBlock
    -- Wait for the server to finish processing blocks.
    liftIO $ atomically $ readTQueue (ccResponse shCommandChannel) >>= \case
        BlockAdded block -> pure block
        _                -> retry

modifySlot :: MonadIO m => (Slot -> Slot) -> ServerHandler -> m Slot
modifySlot f ServerHandler{shCommandChannel} = do
    liftIO $ atomically $ writeTQueue (ccCommand shCommandChannel) $ ModifySlot f
    -- Wait for the server to finish changing the slot.
    liftIO $ atomically $ readTQueue (ccResponse shCommandChannel) >>= \case
        SlotChanged slot -> pure slot
        _                -> retry

addTx :: MonadIO m => ServerHandler -> Tx -> m ()
addTx ServerHandler { shCommandChannel } tx = do
    liftIO $ atomically $ writeTQueue (ccCommand  shCommandChannel) $ AddTx tx

{- Create a thread that keeps the number of blocks in the channel to the maximum
   limit of K -}
pruneChain :: MonadIO m => Integer -> TChan Block -> m ThreadId
pruneChain k original = do
  localChannel <- liftIO $ atomically $ cloneTChan original
  liftIO . forkIO $ go k localChannel
  where
  go :: MonadIO m => Integer -> TChan Block -> m ()
  go k' localChannel = do
    -- Wait for data on the channel
    _ <- liftIO $ atomically $ readTChan localChannel
    if k' == 0
       {- When the counter reaches zero, there are K blocks in the
          original channel and we start to remove the oldest stored
          block by reading it. -}
       then do
           liftIO $ atomically (readTChan original) >> go 0 localChannel
       else do
           go (k' - 1) localChannel

handleCommand ::
    MonadIO m
 => Trace IO MockServerLogMsg
 -> CommandChannel
 -> MVar MockNodeServerChainState
 -> m ()
handleCommand trace CommandChannel {ccCommand, ccResponse} mvChainState =
    liftIO (atomically $ readTQueue ccCommand) >>= \case
        AddTx tx     -> do
            liftIO $ modifyMVar_ mvChainState (pure . over txPool (tx :))
        ModifySlot f -> liftIO $ do
            state <- liftIO $ takeMVar mvChainState
            (s, nextState') <- liftIO $ Chain.modifySlot f
                  & interpret handleControlChain
                  & interpret (LM.handleLogMsgTraceMap ProcessingChainEvent trace)
                  & runState state
                  & runM
            putMVar mvChainState nextState'
            atomically $ do
                writeTQueue ccResponse (SlotChanged s)
        ProcessBlock -> liftIO $ do
            state <- liftIO $ takeMVar mvChainState
            (block, nextState') <- liftIO $ Chain.processBlock
                  & interpret handleControlChain
                  & interpret (LM.handleLogMsgTraceMap ProcessingChainEvent trace)
                  & runState state
                  & runM
            putMVar mvChainState nextState'
            atomically $
                writeTQueue ccResponse (BlockAdded block)

{- | Start the server in a new thread, and return a server handler
     used to control the server -}
runServerNode ::
    MonadIO m
 => Trace IO MockServerLogMsg
 -> FilePath
 -> Integer
 -> MockNodeServerChainState
 -> m ServerHandler
runServerNode trace shSocketPath k initialState = liftIO $ do
    serverState      <- newMVar initialState
    shCommandChannel <- CommandChannel <$> newTQueueIO <*> newTQueueIO
    globalChannel    <- getChannel serverState
    void $ forkIO . void    $ protocolLoop        shSocketPath     serverState
    void $ forkIO . forever $ handleCommand trace shCommandChannel serverState
    void                    $ pruneChain k globalChannel
    pure $ ServerHandler { shSocketPath, shCommandChannel }

-- * ChainSync protocol

{- A monad for running all code executed when a state
   transition is invoked. It makes the implementation of
   state transitions easier to read. -}

type ChainSyncMonad = ReaderT (MVar MockNodeServerChainState) IO

runChainSync :: MVar MockNodeServerChainState -> ChainSyncMonad a -> IO a
runChainSync = flip runReaderT

{- The initial state of the protocol. You can move into
   requesting the next block or reset state by searching for an
   intersection. -}
idleState ::
    ( MonadReader (MVar MockNodeServerChainState) m
    , MonadIO m )
 => LocalChannel
 -> m (ServerStIdle Block (Point Block) Tip m ())
idleState channel' =
    pure ServerStIdle {
        recvMsgRequestNext = nextState channel',
        recvMsgFindIntersect = findIntersect,
        recvMsgDoneClient = return ()
    }

{- Get the next block, either immediately (the Just/Left branch)
   or within a monad (IO, in our case) where you can wait for the
   next block (Nothing/Right branch) -}
nextState ::
    ( MonadReader (MVar MockNodeServerChainState) m
    , MonadIO m )
 => LocalChannel
 -> m (Either (ServerStNext Block (Point Block) Tip m ())
              (m (ServerStNext Block (Point Block) Tip m ())))
nextState localChannel@(LocalChannel channel') = do
    chainState <- ask
    tip' <- getTip chainState
    (liftIO . atomically $ tryReadTChan channel') >>= \case
        Nothing -> do
            Right . pure <$> do
                nextBlock <- liftIO . atomically $ readTChan channel'
                liftIO $ modifyMVar_ chainState (pure . (tip ?~ nextBlock))
                sendRollForward localChannel tip' nextBlock
        Just nextBlock -> do
            liftIO $ modifyMVar_ chainState (pure . (tip ?~ nextBlock))
            Left <$> sendRollForward localChannel tip' nextBlock

{- This protocol state will search for a block intersection
   with some client provided blocks. When an intersection is found
   the client state is reset to the new offset (the Just branch)
   or to the genesis block if no intersection was found. -}
findIntersect ::
    ( MonadReader (MVar MockNodeServerChainState) m
    , MonadIO m )
 => [Point Block]
 -> m (ServerStIntersect Block (Point Block) Tip m ())
findIntersect clientPoints = do
    mvState <- ask
    chainState <- liftIO $ readMVar mvState
    serverPoints <- getChainPoints (view channel chainState) chainState
    let point = listToMaybe
              $ intersect serverPoints
                          clientPoints
    tip' <- getTip mvState
    pure $ case point of
        Nothing ->
          SendMsgIntersectNotFound
            tip'
            -- No intersection found. Resume from origin.
            (ChainSyncServer $ cloneChainFrom 0 >>= idleState)
        Just point' ->
          SendMsgIntersectFound
            point'
            tip'
            -- Resuming from point'.
            (ChainSyncServer $ cloneChainFrom (pointOffset point') >>= idleState)

{- This is a wrapper around the creation of a `ServerStNext` -}
sendRollForward ::
    ( MonadReader (MVar MockNodeServerChainState) m
    , MonadIO m )
 => LocalChannel
 -> Block -- tip
 -> Block -- current
 -> m (ServerStNext Block (Point Block) Tip m ())
sendRollForward channel' tip' current = pure $
    SendMsgRollForward
        current
        tip'
        (ChainSyncServer (idleState channel'))

{- This is the state for a new connection. For now we start with
   slot 0, and in idleState. This will probably change, since it
   makes more sense to start in the `StIntersect` state. -}
chainSyncServer ::
    ( MonadReader (MVar MockNodeServerChainState) m
    , MonadIO m )
 => ChainSyncServer Block (Point Block) Tip m ()
chainSyncServer =
    ChainSyncServer (cloneChainFrom 0 >>= idleState)

{- Use a `TChan` to model a broadcast channel of which we
   clone (with potentially varying offsets) for clients. -}
cloneChainFrom :: forall m.
    ( MonadReader (MVar MockNodeServerChainState) m
    , MonadIO m )
 => Integer
 -> m LocalChannel
cloneChainFrom offset = LocalChannel <$> go
  where
    go :: m (TChan Block)
    go = do
        globalChannel <- ask >>= getChannel
        liftIO $ atomically $ do
            localChannel <- cloneTChan globalChannel
            consume localChannel offset

    consume :: TChan a -> Integer -> STM (TChan a)
    consume channel' ix | ix == 0    = pure channel'
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
    MonadReader (MVar MockNodeServerChainState) m
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
    MonadReader (MVar MockNodeServerChainState) m
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
    MonadReader (MVar MockNodeServerChainState) m
 => ServerStIntersect Block (Point Block) Tip ChainSyncMonad a
 -> m (ServerStIntersect Block (Point Block) Tip IO a)
hoistStIntersect (SendMsgIntersectFound point tip' nextState') =
    SendMsgIntersectFound point tip' <$> hoistChainSync nextState'
hoistStIntersect (SendMsgIntersectNotFound tip' nextState') =
    SendMsgIntersectNotFound tip'    <$> hoistChainSync nextState'

hoistStNext ::
    MonadReader (MVar MockNodeServerChainState) m
 => ServerStNext Block (Point Block) Tip ChainSyncMonad a
 -> m (ServerStNext Block (Point Block) Tip IO a)
hoistStNext (SendMsgRollForward header tip' nextState') =
    SendMsgRollForward header tip' <$> hoistChainSync nextState'
hoistStNext (SendMsgRollBackward header tip' nextState') =
    SendMsgRollBackward header tip' <$> hoistChainSync nextState'

{- This is boilerplate code that sets up the node protocols,
   you can find in:
     ouroboros-network/ouroboros-network/demo/chain-sync.hs -}

protocolLoop ::
    MonadIO m
 => FilePath
 -> MVar MockNodeServerChainState
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
      noTimeLimitsHandshake
      (cborTermVersionDataCodec unversionedProtocolDataCodec)
      acceptableVersion
      (unversionedProtocol (SomeResponderApplication (application internalState)))
      nullErrorPolicies
      $ \_ serverAsync -> wait serverAsync

application ::
    MVar MockNodeServerChainState
 -> OuroborosApplication 'ResponderMode
                         addr
                         LBS.ByteString
                         IO Void ()
application mvChainState =
    mkApplication [ (chainSyncMiniProtocolNum   , chainSync)
                  , (txSubmissionMiniProtocolNum, txSubmission) ]
    where
        chainSync :: RunMiniProtocol 'ResponderMode LBS.ByteString IO Void ()
        chainSync =
             ResponderProtocolOnly $
             MuxPeer
               nullTracer
               codecChainSync
               (ChainSync.chainSyncServerPeer
                   (runReader (hoistChainSync chainSyncServer)
                              mvChainState))

        txSubmission :: RunMiniProtocol 'ResponderMode LBS.ByteString IO Void ()
        txSubmission =
            ResponderProtocolOnly $
            MuxPeer
              nullTracer
              codecTxSubmission
              (TxSubmission.localTxSubmissionServerPeer
                  (pure $ txSubmissionServer mvChainState))

-- * Computing intersections

-- Given a `Point` find its offset into the chain.
pointOffset :: Point Block
            -> Integer
pointOffset pt =
  case pointSlot pt of
    Origin        -> 0
    At (SlotNo s) -> fromIntegral s

-- Currently selects all points from the blockchain.
getChainPoints :: MonadIO m => TChan Block -> MockNodeServerChainState -> m [Point Block]
getChainPoints ch st = do
  chain <- chainNewestFirst ch
  pure $ zipWith mkPoint
    [(st ^. currentSlot) .. 0]
    chain
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
    MVar MockNodeServerChainState
 -> TxSubmission.LocalTxSubmissionServer Tx String IO ()
txSubmissionServer state = txSubmissionState
    where
      txSubmissionState :: TxSubmission.LocalTxSubmissionServer Tx String IO ()
      txSubmissionState =
        TxSubmission.LocalTxSubmissionServer {
          TxSubmission.recvMsgSubmitTx =
            \tx -> do
                modifyMVar_ state (pure . over txPool (addTxToPool tx))
                return (TxSubmission.SubmitSuccess, txSubmissionState)
        , TxSubmission.recvMsgDone     = ()
        }
