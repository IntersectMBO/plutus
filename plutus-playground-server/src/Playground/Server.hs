{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE ScopedTypeVariables   #-}

module Playground.Server
    ( mkHandlers
    , doAnnotateBlockchain
    ) where

import           Control.Monad.Except         (runExceptT, throwError)
import           Control.Monad.IO.Class       (liftIO)
import           Control.Monad.Logger         (MonadLogger, logInfoN)
import qualified Data.ByteString.Lazy.Char8   as BSL
import           Data.Time.Units              (Microsecond, fromMicroseconds)
import           Language.Haskell.Interpreter (InterpreterError (CompilationErrors), InterpreterResult,
                                               SourceCode (SourceCode))
import qualified Language.Haskell.Interpreter as Interpreter
import           Playground.API               (API)
import qualified Playground.Interpreter       as PI
import           Playground.Types             (CompilationResult, Evaluation, EvaluationResult, PlaygroundError)
import           Playground.Usecases          (vesting)
import           Servant                      (err400, errBody)
import           Servant.API                  ((:<|>) ((:<|>)))
import           Servant.Server               (Handler, Server)
import           Wallet.Rollup                (doAnnotateBlockchain)

acceptSourceCode ::
       SourceCode
    -> Handler (Either InterpreterError (InterpreterResult CompilationResult))
acceptSourceCode sourceCode = do
    let maxInterpretationTime :: Microsecond =
            fromMicroseconds (80 * 1000 * 1000)
    r <- liftIO . runExceptT $ PI.compile maxInterpretationTime sourceCode
    case r of
        Right vs -> pure . Right $ vs
        Left (CompilationErrors errors) ->
            pure . Left $ CompilationErrors errors
        Left e -> throwError $ err400 {errBody = BSL.pack . show $ e}

runFunction :: Evaluation -> Handler (Either PlaygroundError EvaluationResult)
runFunction evaluation = do
    let maxInterpretationTime :: Microsecond =
            fromMicroseconds (80 * 1000 * 1000)
    result <-
        liftIO . runExceptT $ PI.runFunction maxInterpretationTime evaluation
    pure $ Interpreter.result <$> result

checkHealth :: Handler ()
checkHealth = do
    res <- acceptSourceCode . SourceCode $ vesting
    case res of
        Left e  -> throwError $ err400 {errBody = BSL.pack . show $ e}
        Right _ -> pure ()

{-# ANN mkHandlers
          ("HLint: ignore Avoid restricted function" :: String)
        #-}

mkHandlers :: MonadLogger m => m (Server API)
mkHandlers = do
    logInfoN "Interpreter ready"
    pure $ acceptSourceCode :<|> runFunction :<|> checkHealth
