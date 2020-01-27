{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}

module Cardano.Node.MockServer where

import           Cardano.Node.API         (API)
import           Control.Concurrent       (forkIO, threadDelay)
import           Control.Concurrent.MVar  (MVar, newMVar, putMVar, takeMVar)
import           Control.Lens             (view)
import           Control.Monad            (forever, void)
import           Control.Monad.Except     (ExceptT (ExceptT), runExceptT, throwError)
import           Control.Monad.IO.Class   (MonadIO, liftIO)
import           Control.Monad.Logger     (MonadLogger, logInfoN)
import           Control.Monad.State      (StateT, get, gets, put, runStateT)
import qualified Data.ByteString.Lazy     as BL
import           Data.Proxy               (Proxy (Proxy))
import           Data.Text                (Text)
import qualified Data.Text.Encoding       as Text
import           Data.Time.Units          (Second, toMicroseconds)
import           Ledger                   (Slot)
import qualified Ledger.Blockchain        as Blockchain
import           Network.Wai.Handler.Warp (run)
import           Plutus.SCB.Arbitrary     ()
import           Plutus.SCB.Utils         (tshow)
import           Servant                  ((:<|>) ((:<|>)), Application, Handler (Handler), NoContent (NoContent),
                                           err500, errBody, hoistServer, serve)
import           Wallet.Emulator          (EmulatorState, MonadEmulator, emptyEmulatorState)
import qualified Wallet.Emulator          as EM

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
       MVar EmulatorState
    -> StateT EmulatorState (ExceptT Text IO) a
    -> IO (Either Text a)
asThread stateVar action = stepState stateVar runAction
  where
    runAction oldState = do
        result <- runExceptT $ runStateT action oldState
        case result of
            Left err                -> pure (Left err, oldState)
            Right (value, newState) -> pure (Right value, newState)

activitySimulator :: MVar EmulatorState -> IO ()
activitySimulator stateVar =
    forever $ do
        void $ asThread stateVar addBlock
        threadDelay $ fromIntegral $ toMicroseconds (5 :: Second)

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
        (healthcheck :<|> (getCurrentSlot :<|> addBlock))

main :: (MonadIO m, MonadLogger m) => m ()
main = do
    let port = 8082
    stateVar <- liftIO $ newMVar emptyEmulatorState
    logInfoN "Starting activity simulation thread."
    void $ liftIO $ forkIO $ activitySimulator stateVar
    logInfoN $ "Starting mock node server on port: " <> tshow port
    liftIO $ run port $ app stateVar
