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

import           API                          (API, RunResult)
import           Control.Monad.Catch          (MonadCatch, MonadMask, bracket, catch)
import           Control.Monad.Except         (MonadError, runExceptT, throwError)
import           Control.Monad.IO.Class       (MonadIO, liftIO)
import           Control.Monad.Logger         (MonadLogger, logInfoN)
import           Data.Aeson                   (ToJSON, encode)
import qualified Data.ByteString.Char8        as BS
import qualified Data.ByteString.Lazy.Char8   as BSL
import qualified Data.Text                    as Text
import           Data.Time.Units              (Microsecond, fromMicroseconds)
import qualified Interpreter
import           Language.Haskell.Interpreter (InterpreterError (CompilationErrors), InterpreterResult,
                                               SourceCode (SourceCode))
import           Meadow.Contracts             (escrow)
import           Network.HTTP.Types           (hContentType)
import           Servant                      (ServantErr, err400, errBody, errHeaders)
import           Servant.API                  ((:<|>) ((:<|>)), (:>), JSON, Post, ReqBody)
import           Servant.Server               (Handler, Server)
import           System.Timeout               (timeout)

acceptSourceCode :: SourceCode -> Handler (Either InterpreterError (InterpreterResult RunResult))
acceptSourceCode sourceCode = do
    let maxInterpretationTime :: Microsecond = fromMicroseconds (10 * 1000 * 1000)
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

{-# ANN mkHandlers
          ("HLint: ignore Avoid restricted function" :: String)
        #-}

mkHandlers :: (MonadLogger m, MonadIO m) => m (Server API)
mkHandlers = do
    logInfoN "Interpreter ready"
    pure $ acceptSourceCode :<|> checkHealth
