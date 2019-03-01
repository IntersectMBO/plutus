{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# OPTIONS_GHC   -Wno-orphans #-}

module Server
    ( mkHandlers
    )
where

import           API                          (API, MeadowError (CompilationErrors, MeadowTimeout), RunResult,
                                               SourceCode (SourceCode))
import           Control.Monad.Catch          (MonadCatch, MonadMask, bracket, catch)
import           Control.Monad.Except         (MonadError, runExceptT, throwError)
import           Control.Monad.IO.Class       (MonadIO, liftIO)
import           Control.Monad.Logger         (MonadLogger, logInfoN)
import           Data.Aeson                   (ToJSON, encode)
import qualified Data.ByteString.Char8        as BS
import qualified Data.ByteString.Lazy.Char8   as BSL
import qualified Data.Text                    as Text
import qualified Interpreter
import           Language.Haskell.Interpreter (CompilationError)
import           Meadow.Contracts             (basicContract)
import           Network.HTTP.Types           (hContentType)
import           Servant                      (ServantErr, err400, errBody, errHeaders)
import           Servant.API                  ((:<|>) ((:<|>)), (:>), JSON, Post, ReqBody)
import           Servant.Server               (Handler, Server)
import           System.Timeout               (timeout)

acceptSourceCode :: SourceCode -> Handler (Either [CompilationError] RunResult)
acceptSourceCode sourceCode = do
    let maxInterpretationTime = 5000000
    r <-
        liftIO
        . timeoutInterpreter maxInterpretationTime
        $ runExceptT
        $ Interpreter.runHaskell sourceCode
    case r of
        Right vs                        -> pure $ Right vs
        Left (CompilationErrors errors) -> pure . Left $ errors
        Left  e                         -> throwError $ err400 { errBody = BSL.pack . show $ e }

throwJSONError :: (MonadError ServantErr m, ToJSON a) => ServantErr -> a -> m b
throwJSONError err json = throwError
    $ err { errBody = encode json, errHeaders = [jsonHeader] }
    where jsonHeader = (hContentType, "application/json;charset=utf-8")

checkHealth :: Handler ()
checkHealth = do
    res <- acceptSourceCode . SourceCode . Text.pack . BS.unpack $ basicContract
    case res of
        Left e  -> throwError $ err400 {errBody = BSL.pack . show $ e}
        Right _ -> pure ()

timeoutInterpreter :: Int -> IO (Either MeadowError a) -> IO (Either MeadowError a)
timeoutInterpreter n action = do
    res <- timeout n action
    case res of
        Nothing -> pure . Left $ MeadowTimeout
        Just a  -> pure a

{-# ANN mkHandlers
          ("HLint: ignore Avoid restricted function" :: String)
        #-}

mkHandlers :: (MonadLogger m, MonadIO m) => m (Server API)
mkHandlers = do
    logInfoN "Interpreter ready"
    pure $ acceptSourceCode :<|> checkHealth
