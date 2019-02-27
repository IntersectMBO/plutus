{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# OPTIONS_GHC   -Wno-orphans #-}

module Playground.Server
    ( mkHandlers
    ) where

import           Control.Monad.Except         (MonadError, runExceptT, throwError)
import           Control.Monad.IO.Class       (liftIO)
import           Control.Monad.Logger         (MonadLogger, logInfoN)
import           Data.Aeson                   (ToJSON, encode)
import qualified Data.ByteString.Char8        as BS
import qualified Data.ByteString.Lazy.Char8   as BSL
import qualified Data.Text                    as Text
import           Language.Haskell.Interpreter (CompilationError)
import           Network.HTTP.Types           (hContentType)
import           Playground.API               (API, CompilationResult, Evaluation, EvaluationResult (EvaluationResult),
                                               PlaygroundError (PlaygroundTimeout), PlaygroundError (PlaygroundTimeout),
                                               SourceCode (SourceCode), SourceCode, parseErrorText, parseErrorText)
import qualified Playground.API               as PA
import qualified Playground.Interpreter       as PI
import           Playground.Usecases          (vesting)
import           Servant                      (ServantErr, err400, errBody, errHeaders)
import           Servant.API                  ((:<|>) ((:<|>)))
import           Servant.Server               (Handler, Server)
import           System.Timeout               (timeout)
import qualified Wallet.Graph                 as V

acceptSourceCode ::
       SourceCode -> Handler (Either [CompilationError] CompilationResult)
acceptSourceCode sourceCode = do
    let maxInterpretationTime = 5000000
    r <-
        liftIO . timeoutInterpreter maxInterpretationTime $
        runExceptT $ PI.compile sourceCode
    case r of
        Right vs -> pure . Right $ vs
        Left (PA.InterpreterError errors) ->
            pure $ Left $ map (parseErrorText . Text.pack) errors
        Left (PA.CompilationErrors errors) -> pure . Left $ errors
        Left e -> throwError $ err400 {errBody = BSL.pack . show $ e}

throwJSONError :: (MonadError ServantErr m, ToJSON a) => ServantErr -> a -> m b
throwJSONError err json =
    throwError $ err {errBody = encode json, errHeaders = [jsonHeader]}
  where
    jsonHeader = (hContentType, "application/json;charset=utf-8")

runFunction :: Evaluation -> Handler EvaluationResult
runFunction evaluation = do
    let maxInterpretationTime = 10000000
    result <-
        liftIO . timeoutInterpreter maxInterpretationTime $
        runExceptT $ PI.runFunction evaluation
    let pubKeys = PA.pubKeys evaluation
    case result of
        Right (blockchain, emulatorLog, fundsDistribution) -> do
            let flowgraph = V.graph $ V.txnFlows pubKeys blockchain
            pure $
                EvaluationResult
                    blockchain
                    flowgraph
                    emulatorLog
                    fundsDistribution
        Left (PA.InterpreterError errors) ->
            throwJSONError err400 $ map (parseErrorText . Text.pack) errors
        Left err -> throwError $ err400 {errBody = BSL.pack . show $ err}

checkHealth :: Handler ()
checkHealth = do
    res <- acceptSourceCode . SourceCode . Text.pack . BS.unpack $ vesting
    case res of
        Left e  -> throwError $ err400 {errBody = BSL.pack . show $ e}
        Right _ -> pure ()

timeoutInterpreter ::
       Int -> IO (Either PlaygroundError a) -> IO (Either PlaygroundError a)
timeoutInterpreter n action = do
    res <- timeout n action
    case res of
        Nothing -> pure . Left $ PlaygroundTimeout
        Just a  -> pure a

{-# ANN mkHandlers
          ("HLint: ignore Avoid restricted function" :: String)
        #-}

mkHandlers :: MonadLogger m => m (Server API)
mkHandlers = do
    logInfoN "Interpreter ready"
    pure $ acceptSourceCode :<|> runFunction :<|> checkHealth
