{-# LANGUAGE NamedFieldPuns      #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}

module Cardano.Node.MockServer where

import           Cardano.Node.API          (API)
import           Control.Concurrent        (forkIO, threadDelay)
import           Control.Concurrent.MVar   (MVar, newMVar, putMVar, takeMVar)
import           Control.Lens              (view, (%=))
import           Control.Monad             (forever, void)
import           Control.Monad.Except      (ExceptT (ExceptT), runExceptT, throwError)
import           Control.Monad.IO.Class    (MonadIO, liftIO)
import           Control.Monad.Logger      (MonadLogger, logDebugN, logInfoN, runStdoutLoggingT)
import           Control.Monad.State       (StateT, get, gets, put, runStateT)
import qualified Data.ByteString.Lazy      as BL
import           Data.Proxy                (Proxy (Proxy))
import           Data.Text                 (Text)
import qualified Data.Text.Encoding        as Text
import           Data.Text.Prettyprint.Doc (Pretty (pretty))
import           Data.Time.Units           (Second, toMicroseconds)
import           Ledger                    (Slot, Tx)
import qualified Ledger
import qualified Ledger.Blockchain         as Blockchain
import           Network.Wai.Handler.Warp  (run)
import           Plutus.SCB.Arbitrary      ()
import           Plutus.SCB.Utils          (tshow)
import           Servant                   ((:<|>) ((:<|>)), Application, Handler (Handler), NoContent (NoContent),
                                            err500, errBody, hoistServer, serve)
import           Wallet.Emulator           (EmulatorState, MonadEmulator, emptyEmulatorState)
import qualified Wallet.Emulator           as EM

data MockServerConfig =
    MockServerConfig
        { mscPort :: Int
        , mscSlotLength :: Second
        }

defaultConfig :: MockServerConfig
defaultConfig =
    MockServerConfig
        { mscPort = 8082
        , mscSlotLength = 5
        }

healthcheck :: Monad m => m NoContent
healthcheck = pure NoContent

getCurrentSlot :: MonadEmulator e m => m Slot
getCurrentSlot =
    gets (Blockchain.lastSlot . view (EM.chainState . EM.chainNewestFirst))

addBlock :: MonadEmulator e m => m Slot
addBlock = do
    chainState <- get
    let (value, newState) =
            EM.runEmulator chainState $
            EM.EmulatorAction $ EM.processEmulated $ EM.addBlocks 1
    case value of
        Left err -> throwError err
        Right _ -> do
            put newState
            getCurrentSlot

addTx :: (MonadLogger m, MonadEmulator e m) => Tx -> m NoContent
addTx tx = do
    logInfoN  $ "Adding tx " <> tshow (Ledger.txId tx)
    logDebugN $ tshow (pretty tx)
    EM.chainState . EM.txPool %= (tx:) >> pure NoContent

------------------------------------------------------------
asHandler ::
       MVar EmulatorState
    -> StateT EmulatorState (ExceptT Text IO) a
    -> Handler a
asHandler stateVar action = Handler . ExceptT $ stepState stateVar runAction
  where
    runAction oldState = do
        result <- runExceptT $ runStateT action oldState
        case result of
            Left err ->
                pure
                    ( Left $
                      err500 {errBody = BL.fromStrict $ Text.encodeUtf8 err}
                    , oldState)
            Right (value, newState) -> pure (Right value, newState)

asThread ::
    ( MonadIO m )
    => MVar EmulatorState
    -> StateT EmulatorState (ExceptT Text m) a
    -> m (Either Text a)
asThread stateVar action = stepState stateVar runAction
  where
    runAction oldState = do
        result <- runExceptT $ runStateT action oldState
        case result of
            Left err                -> pure (Left err, oldState)
            Right (value, newState) -> pure (Right value, newState)

-- | Calls 'addBlock' at the start of every slot, causing pending transactions
--   to be validated and added to the chain.
slotCoordinator :: 
    ( MonadIO m
    , MonadLogger m
    )
    => MockServerConfig
    -> MVar EmulatorState
    -> m ()
slotCoordinator MockServerConfig{mscSlotLength} stateVar =
    forever $ do
        logDebugN "Adding slot"
        void $ asThread stateVar addBlock
        liftIO $ threadDelay $ fromIntegral $ toMicroseconds mscSlotLength

stepState :: MonadIO m => MVar a -> (a -> m (b, a)) -> m b
stepState stateVar action = do
    oldState <- liftIO $ takeMVar stateVar
    (value, newState) <- action oldState
    liftIO $ putMVar stateVar newState
    pure value

app :: MVar EmulatorState -> Application
app stateVar =
    serve (Proxy @API) $
    hoistServer
        (Proxy @API)
        (asHandler stateVar)
        (healthcheck
        :<|> runStdoutLoggingT . addTx
        :<|> getCurrentSlot)

main :: (MonadIO m, MonadLogger m) => MockServerConfig -> m ()
main config = do
    let MockServerConfig{mscPort} = config
    stateVar <- liftIO $ newMVar emptyEmulatorState
    logInfoN "Starting slot coordination thread."
    void $ liftIO $ forkIO $ runStdoutLoggingT $ slotCoordinator defaultConfig stateVar
    logInfoN $ "Starting mock node server on port: " <> tshow mscPort
    liftIO $ run mscPort $ app stateVar
