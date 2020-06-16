{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE LambdaCase            #-}
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
import           Data.Time.Units              (Second)
import           Language.Haskell.Interpreter (InterpreterError (CompilationErrors), InterpreterResult, SourceCode)
import qualified Language.Haskell.Interpreter as Interpreter
import           Playground.API               (API)
import qualified Playground.Interpreter       as PI
import           Playground.Types             (CompilationResult, Evaluation, EvaluationResult, PlaygroundError)
import           Playground.Usecases          (vesting)
import           Servant                      (err400, errBody)
import           Servant.API                  ((:<|>) ((:<|>)))
import           Servant.Server               (Handler, Server)
import           Wallet.Rollup                (doAnnotateBlockchain)

maxInterpretationTime :: Second
maxInterpretationTime = 80

compileSourceCode ::
       SourceCode
    -> Handler (Either InterpreterError (InterpreterResult CompilationResult))
compileSourceCode sourceCode = do
    r <- liftIO . runExceptT $ PI.compile maxInterpretationTime sourceCode
    case r of
        Right vs -> pure . Right $ vs
        Left (CompilationErrors errors) ->
            pure . Left $ CompilationErrors errors
        Left e -> throwError $ err400 {errBody = BSL.pack . show $ e}

evaluateSimulation ::
       Evaluation -> Handler (Either PlaygroundError EvaluationResult)
evaluateSimulation evaluation = do
    result <-
        liftIO . runExceptT $
        PI.evaluateSimulation maxInterpretationTime evaluation
    pure $ Interpreter.result <$> result

checkHealth :: Handler ()
checkHealth =
    compileSourceCode vesting >>= \case
        Left e -> throwError $ err400 {errBody = BSL.pack . show $ e}
        Right _ -> pure ()

mkHandlers :: MonadLogger m => m (Server API)
mkHandlers = do
    logInfoN "Interpreter ready"
    pure $ compileSourceCode :<|> evaluateSimulation :<|> checkHealth
