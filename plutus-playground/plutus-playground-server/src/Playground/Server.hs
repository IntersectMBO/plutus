{-# LANGUAGE DeriveGeneric         #-}
{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# OPTIONS_GHC   -Wno-orphans #-}

module Playground.Server
    ( mkHandlers
    , mkInterpreterInstance
    , runInterpreterInstance
    ) where

import           Control.Concurrent.MVar             (MVar, newMVar, withMVar)
import           Control.Monad.Catch                 (catch)
import           Control.Monad.Except                (ExceptT, MonadError, catchError, runExceptT, throwError)
import           Control.Monad.IO.Class              (liftIO)
import           Control.Monad.Trans.Class           (lift)
import           Control.Newtype.Generics            (Newtype, unpack)
import           Data.Aeson                          (ToJSON, encode)
import qualified Data.ByteString.Lazy.Char8          as BSL
import qualified Data.Text                           as Text
import           GHC.Generics                        (Generic)
import           Language.Haskell.Interpreter        (InterpreterError (WontCompile), InterpreterT, errMsg)
import qualified Language.Haskell.Interpreter        as Interpreter
import           Language.Haskell.Interpreter.Unsafe (unsafeRunInterpreterWithArgsLibdir)
import           Network.HTTP.Types                  (hContentType)
import           Playground.API                      (API, CompilationError, Evaluation,
                                                      EvaluationResult (EvaluationResult), FunctionSchema,
                                                      FunctionSchema, PlaygroundError (PlaygroundTimeout),
                                                      SimpleArgumentSchema, SourceCode, parseErrorText,
                                                      toSimpleArgumentSchema)
import qualified Playground.API                      as PA
import qualified Playground.Interpreter              as PI
import           Servant                             (ServantErr, err400, errBody, errHeaders)
import           Servant.API                         ((:<|>) ((:<|>)))
import           Servant.Server                      (Handler, Server)
import           System.Environment                  (lookupEnv)
import           System.Timeout                      (timeout)
import qualified Wallet.Graph                        as V

newtype InterpreterInstance =
    InterpreterInstance (MVar ())
    deriving (Generic)

instance Newtype InterpreterInstance

mkInterpreterInstance :: IO InterpreterInstance
mkInterpreterInstance = InterpreterInstance <$> newMVar ()

runInterpreterInstance ::
       InterpreterInstance
    -> InterpreterT (ExceptT PlaygroundError IO) a
    -> IO (Either PlaygroundError a)
runInterpreterInstance i = withMVar (unpack i) . const . runInterpreter

runInterpreter ::
       InterpreterT (ExceptT PlaygroundError IO) a
    -> IO (Either PlaygroundError a)
runInterpreter action = do
    mLibDir <- liftIO $ lookupEnv "GHC_LIB_DIR"
    runPlayground $
        case mLibDir of
            Just libDir -> unsafeRunInterpreterWithArgsLibdir [] libDir action
      -- TODO: We can make parsing easier by dumping json
      -- unsafeRunInterpreterWithArgsLibdir ["-ddump-json"] libDir action
            Nothing     -> Interpreter.runInterpreter action

instance MonadError PlaygroundError (InterpreterT (ExceptT PlaygroundError IO)) where
    throwError = lift . throwError
    catchError action _ = catch action (throwError . PA.InterpreterError)

runPlayground ::
       ExceptT PlaygroundError IO (Either InterpreterError a)
    -> IO (Either PlaygroundError a)
runPlayground action = do
    r <- runExceptT action
    case r of
        Right (Right a) -> pure . Right $ a
        Right (Left e)  -> pure . Left . PA.InterpreterError $ e
        Left e          -> pure . Left $ e

acceptSourceCode ::
       InterpreterInstance
    -> SourceCode
    -> Handler (Either [CompilationError] [FunctionSchema SimpleArgumentSchema])
acceptSourceCode i sourceCode = do
    r <-
        liftIO . timeoutInterpreter 5000000 . runInterpreterInstance i $
        PI.compile sourceCode
    case r of
        Right vs -> pure . Right $ fmap toSimpleArgumentSchema <$> vs
        Left (PA.InterpreterError (WontCompile errors)) ->
            pure $ Left $ map (parseErrorText . Text.pack . errMsg) errors
        Left e -> throwError $ err400 {errBody = BSL.pack . show $ e}

throwJSONError :: (MonadError ServantErr m, ToJSON a) => ServantErr -> a -> m b
throwJSONError err json =
    throwError $ err {errBody = encode json, errHeaders = [jsonHeader]}
  where
    jsonHeader = (hContentType, "application/json;charset=utf-8")

runFunction :: InterpreterInstance -> Evaluation -> Handler EvaluationResult
runFunction interpreter evaluation = do
    result <-
        liftIO . timeoutInterpreter 10000000 $
        runInterpreterInstance interpreter $ PI.runFunction evaluation
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
        Left (PA.InterpreterError (WontCompile errors)) ->
            throwJSONError err400 $
            map (parseErrorText . Text.pack . errMsg) errors
        Left err -> throwError $ err400 {errBody = BSL.pack . show $ err}

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

mkHandlers :: IO (Server API)
mkHandlers = do
    interpreter <- mkInterpreterInstance
    liftIO . putStrLn $ "warming up"
    warmupResult <- liftIO $ runInterpreterInstance interpreter PI.warmup
    case warmupResult of
        Left e  -> error $ "failed to warmup interpreter with error: " <> show e
        Right _ -> liftIO . putStrLn $ "successfully warmed up interpreter"
    pure $ acceptSourceCode interpreter :<|> runFunction interpreter
