{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeOperators         #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Server
  ( mkHandlers,
  )
where

import           API                                              (API, CheckForWarnings (CheckForWarnings),
                                                                   MarloweSymbolicAPI, RunResult)
import           Control.Concurrent                               (forkIO, threadDelay)
import           Control.Concurrent.STM                           (atomically)
import           Control.Concurrent.STM.TVar                      (TVar, modifyTVar, readTVarIO)
import           Control.Monad                                    (forever, void, when)
import           Control.Monad.Catch                              (MonadCatch, MonadMask, bracket, catch)
import           Control.Monad.Except                             (MonadError, runExceptT, throwError)
import           Control.Monad.IO.Class                           (MonadIO, liftIO)
import           Control.Monad.Logger                             (MonadLogger, logInfoN)
import           Data.Aeson                                       (ToJSON, eitherDecode, encode)
import qualified Data.ByteString.Char8                            as BS
import qualified Data.ByteString.Lazy.Char8                       as BSL
import           Data.Maybe                                       (fromMaybe)
import           Data.Proxy                                       (Proxy (Proxy))
import           Data.Text                                        (Text)
import qualified Data.Text                                        as Text
import           Data.Time.Units                                  (Second)
import qualified Data.UUID                                        as UUID
import           Data.UUID.V4                                     (nextRandom)
import qualified Interpreter
import           Language.Haskell.Interpreter                     (InterpreterError (CompilationErrors),
                                                                   InterpreterResult, SourceCode (SourceCode))
import           Language.Marlowe                                 (Contract)
import           Language.Marlowe.ACTUS.Definitions.ContractTerms (ContractTerms)
import           Language.Marlowe.ACTUS.Generator                 (genFsContract, genStaticContract)
import           Language.Marlowe.Pretty
import           Marlowe.Contracts                                (escrow)
import qualified Marlowe.Symbolic.Types.Request                   as MSReq
import qualified Marlowe.Symbolic.Types.Response                  as MSRes
import           Network.HTTP.Types                               (hContentType)
import           Servant                                          (ServerError, err400, err500, errBody, errHeaders)
import           Servant.API                                      ((:<|>) ((:<|>)), (:>), JSON, NoContent (NoContent),
                                                                   Post, ReqBody)
import           Servant.Client                                   (ClientEnv, ClientM, client, runClientM)
import           Servant.Server                                   (Handler, Server)
import           System.Timeout                                   (timeout)

acceptSourceCode :: SourceCode -> Handler (Either InterpreterError (InterpreterResult RunResult))
acceptSourceCode sourceCode = do
  let maxInterpretationTime = 10 :: Second
  r <-
    liftIO $
      runExceptT $
        Interpreter.runHaskell maxInterpretationTime sourceCode
  case r of
    Right vs                        -> pure $ Right vs
    Left (CompilationErrors errors) -> pure . Left $ CompilationErrors errors
    Left e                          -> throwError $ err400 {errBody = BSL.pack . show $ e}

checkHealth :: Handler ()
checkHealth = do
  res <- acceptSourceCode . SourceCode . Text.pack . BS.unpack $ escrow
  case res of
    Left e  -> throwError $ err400 {errBody = BSL.pack . show $ e}
    Right _ -> pure ()

marloweSymbolicApi :: Proxy MarloweSymbolicAPI
marloweSymbolicApi = Proxy

marloweSymbolicClient :: Maybe Text -> Maybe Text -> MSReq.Request -> ClientM MSRes.Response
marloweSymbolicClient = client marloweSymbolicApi

genActusContract :: ContractTerms -> Handler String
genActusContract terms = pure $ show $ pretty $ genFsContract terms

genActusContractStatic :: ContractTerms -> Handler String
genActusContractStatic terms = pure $ show $ pretty $ genStaticContract terms

analyseContract :: Text -> Text -> ClientEnv -> CheckForWarnings -> Handler MSRes.Result
analyseContract apiKey callbackUrl marloweSymbolicClientEnv (CheckForWarnings onlyAssertions contract state) = do
  let req = MSReq.Request "" (Text.unpack callbackUrl) onlyAssertions contract state
  res <- liftIO $ runClientM (marloweSymbolicClient (Just "Event") (Just apiKey) req) marloweSymbolicClientEnv
  case res of
    Left err -> do
      liftIO $ print err
      throwError $ err500 {errBody = BSL.pack "error analysing contract"}
    Right (MSRes.Response _ response) -> pure response

{-# ANN
  mkHandlers
  ("HLint: ignore Avoid restricted function" :: String)
  #-}
mkHandlers :: (MonadLogger m, MonadIO m) => Text -> Text -> ClientEnv -> m (Server API)
mkHandlers apiKey callbackUrl marloweSymbolicClientEnv = do
  logInfoN "Interpreter ready"
  pure $ (acceptSourceCode :<|> checkHealth :<|> genActusContract :<|> genActusContractStatic :<|> analyseContract apiKey callbackUrl marloweSymbolicClientEnv)
