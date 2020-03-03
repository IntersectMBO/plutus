{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeOperators         #-}
{-# OPTIONS_GHC   -Wno-orphans     #-}

module Server
    ( mkHandlers
    )
where

import           API                             (API, MarloweSymbolicAPI, RunResult, WSAPI)
import           Control.Concurrent              (forkIO, threadDelay)
import           Control.Concurrent.STM          (atomically)
import           Control.Concurrent.STM.TVar     (TVar, modifyTVar, readTVarIO)
import           Control.Monad                   (forever, void, when)
import           Control.Monad.Catch             (MonadCatch, MonadMask, bracket, catch)
import           Control.Monad.Except            (MonadError, runExceptT, throwError)
import           Control.Monad.IO.Class          (MonadIO, liftIO)
import           Control.Monad.Logger            (MonadLogger, logInfoN)
import           Data.Aeson                      (ToJSON, eitherDecode, encode)
import qualified Data.ByteString.Char8           as BS
import qualified Data.ByteString.Lazy.Char8      as BSL
import           Data.Maybe                      (fromMaybe)
import           Data.Proxy                      (Proxy (Proxy))
import           Data.Text                       (Text)
import qualified Data.Text                       as Text
import           Data.Time.Units                 (Second)
import qualified Data.UUID                       as UUID
import           Data.UUID.V4                    (nextRandom)
import qualified Interpreter
import           Language.Haskell.Interpreter    (InterpreterError (CompilationErrors), InterpreterResult,
                                                  SourceCode (SourceCode))
import           Marlowe.Contracts               (escrow)
import qualified Marlowe.Symbolic.Types.API      as MS
import qualified Marlowe.Symbolic.Types.Request  as MSReq
import qualified Marlowe.Symbolic.Types.Response as MSRes
import           Network.HTTP.Types              (hContentType)
import           Network.WebSockets.Connection   (Connection, PendingConnection, receiveData, sendTextData)
import           Servant                         (ServantErr, err400, errBody, errHeaders)
import           Servant.API                     ((:<|>) ((:<|>)), (:>), JSON, NoContent (NoContent), Post, ReqBody)
import           Servant.Client                  (ClientEnv, ClientM, client, runClientM)
import           Servant.Server                  (Handler, Server)
import           System.Timeout                  (timeout)
import           WebSocket                       (Registry, WebSocketRequestMessage (CheckForWarnings),
                                                  WebSocketResponseMessage (CheckForWarningsResult, OtherError),
                                                  deleteFromRegistry, finishWaiting, initializeConnection,
                                                  insertIntoRegistry, isWaiting, lookupInRegistry, newRegistry,
                                                  runWithConnection, startWaiting)

acceptSourceCode :: SourceCode -> Handler (Either InterpreterError (InterpreterResult RunResult))
acceptSourceCode sourceCode = do
    let maxInterpretationTime = 10 :: Second
    r <-
        liftIO
        $ runExceptT
        $ Interpreter.runHaskell maxInterpretationTime sourceCode
    case r of
        Right vs                        -> pure $ Right vs
        Left (CompilationErrors errors) -> pure . Left $ CompilationErrors errors
        Left  e                         -> throwError $ err400 { errBody = BSL.pack . show $ e }

checkHealth :: Handler ()
checkHealth = do
    res <- acceptSourceCode . SourceCode . Text.pack . BS.unpack $ escrow
    case res of
        Left e  -> throwError $ err400 {errBody = BSL.pack . show $ e}
        Right _ -> pure ()

marloweSymbolicApi :: Proxy MarloweSymbolicAPI
marloweSymbolicApi = Proxy

marloweSymbolicClient :: Maybe Text -> Maybe Text -> MSReq.Request -> ClientM NoContent
marloweSymbolicClient = client marloweSymbolicApi

-- | Each user (Connection) is only allowed to send one analysis request at a time
--   These requests are sent in a fire and forget manner and the user is informed
--   of the result when the analysis sends a response to the handleNotifcation endpoint
--   We keep a registry of each user and any active request
handleWS :: TVar Registry -> Text -> Text -> ClientEnv -> PendingConnection -> Handler ()
handleWS registryVar apiKey callbackUrl marloweSymbolicClientEnv pending = liftIO $ do
    (uuid, connection) <- initializeConnection pending
    atomically . modifyTVar registryVar $ insertIntoRegistry uuid connection
    putStrLn $ "created connection for user " <> show uuid
    runWithConnection connection (handle connection uuid)
    atomically . modifyTVar registryVar $ deleteFromRegistry uuid
    putStrLn $ "closed connection for user " <> show uuid
    where
        handle :: Connection -> UUID.UUID -> Text -> IO ()
        handle connection uuid msg = do
            let timeoutSeconds = 120
            registry <- readTVarIO registryVar
            available <- case lookupInRegistry uuid registry of
                            Nothing -> do
                                putStrLn $ "Ignoring message because user " <> show uuid <> " seems to have disappeared from the registry"
                                pure False
                            Just (_, Just _) -> do
                                putStrLn $ "Ignoring message because user " <> show uuid <> " already has a request pending"
                                pure False
                            _ -> pure True
            when available $ case eitherDecode (BSL.pack . Text.unpack $ msg) of
                        Left err -> do
                          putStrLn $ "could not decode websocket message: " <> Text.unpack msg
                          sendTextData connection $ encode $ OtherError "Invalid message sent through websocket"
                        Right (CheckForWarnings contract state) -> do
                            let req = MSReq.Request (UUID.toString uuid) (Text.unpack callbackUrl) contract state
                            putStrLn $ "send request for user " <> show uuid <> " to " <> Text.unpack callbackUrl
                            res <- runClientM (marloweSymbolicClient (Just "Event") (Just apiKey) req) marloweSymbolicClientEnv
                            case res of
                                Left err -> do
                                  let errMsg = "error processing marlowe sybolic request: " <> show err
                                  putStrLn errMsg
                                  sendTextData connection $ encode $ OtherError errMsg
                                Right _ ->
                                  -- The analysis was triggered successfully so we will wait until the specified
                                  -- timeout and if the response has still not arrived then we'll let the user know
                                  -- One of these timeout threads is created for every unique analysis request
                                  void . forkIO $ do
                                      -- We set the waiting for this unique request as it is the latest
                                      waiting <- nextRandom
                                      atomically . modifyTVar registryVar $ startWaiting uuid waiting
                                      -- Wait for the timeout
                                      threadDelay (timeoutSeconds * 1000000)
                                      -- If the user is still waiting for the same request then timeout and tell them
                                      registry <- readTVarIO registryVar
                                      if isWaiting uuid waiting registry
                                        then do
                                              putStrLn "analysis request timed out"
                                              sendTextData connection $ encode $ OtherError "Analysis request timed out"
                                              atomically . modifyTVar registryVar $ finishWaiting uuid
                                        else pure ()


handleNotification :: TVar Registry -> MSRes.Response -> Handler NoContent
handleNotification registryVar response = liftIO $ do
    case UUID.fromString $ MSRes.uuid response of
        Nothing -> putStrLn "Response contains an invalid UUID"
        Just uuid -> do
            registry <- readTVarIO registryVar
            case lookupInRegistry uuid registry of
                          Nothing -> putStrLn $ "Ignoring response because user " <> show uuid <> " is not in the registry, they've probably disconnected"
                          Just (_, Nothing) -> putStrLn $ "Ignoring response because user " <> show uuid <> " isn't waiting for one"
                          Just (connection, _) -> do
                              atomically . modifyTVar registryVar $ finishWaiting uuid
                              sendTextData connection $ encode $ CheckForWarningsResult $ MSRes.result response
    pure NoContent


{-# ANN mkHandlers
          ("HLint: ignore Avoid restricted function" :: String)
        #-}

mkHandlers :: (MonadLogger m, MonadIO m) => Text -> Text -> ClientEnv -> m (Server (API :<|> MS.API :<|> WSAPI))
mkHandlers apiKey callbackUrl marloweSymbolicClientEnv = do
    logInfoN "Interpreter ready"
    registry <- liftIO $ atomically newRegistry
    pure $ (acceptSourceCode :<|> checkHealth) :<|> handleNotification registry :<|> handleWS registry apiKey callbackUrl marloweSymbolicClientEnv
