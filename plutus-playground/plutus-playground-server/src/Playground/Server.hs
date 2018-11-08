module Playground.Server
  ( handlers
  ) where

import           Control.Monad.IO.Class              (liftIO)
import           Data.Aeson                          (encode)
import qualified Data.ByteString.Lazy.Char8          as BSL
import           Data.Maybe                          (catMaybes, fromMaybe)
import qualified Data.Text                           as Text
import           Language.Haskell.Interpreter        (InterpreterError (WontCompile), InterpreterT, MonadInterpreter,
                                                      errMsg)
import qualified Language.Haskell.Interpreter        as Interpreter
import           Language.Haskell.Interpreter.Unsafe (unsafeRunInterpreterWithArgsLibdir)
import           Playground.API                      (API, CompilationError, Evaluation, FunctionSchema,
                                                      FunctionsSchema (FunctionsSchema), SourceCode, parseErrorText)
import qualified Playground.Interpreter              as PI
import           Servant                             (err400, errBody, throwError)
import           Servant.API                         ((:<|>) ((:<|>)), NoContent (NoContent))
import           Servant.Server                      (Handler, Server)
import           System.Environment                  (lookupEnv)
import           Wallet.UTXO.Types                   (Blockchain)

runInterpreter :: InterpreterT IO a -> IO (Either InterpreterError a)
runInterpreter action = do
  mLibDir <- liftIO $ lookupEnv "GHC_LIB_DIR"
  case mLibDir of
    Just libDir ->
      unsafeRunInterpreterWithArgsLibdir [] libDir action
      -- TODO: We can make parsing easier by dumping json
      -- unsafeRunInterpreterWithArgsLibdir ["-ddump-json"] libDir action
    Nothing -> Interpreter.runInterpreter action

acceptSourceCode ::
     SourceCode -> Handler (Either [CompilationError] [FunctionSchema])
acceptSourceCode sourceCode = do
  r <- liftIO . runInterpreter $ PI.compile sourceCode
  case r of
    Right v -> pure (Right v)
    Left (WontCompile errors) ->
      pure $ Left $ map (parseErrorText . Text.pack . errMsg) errors
    Left e -> throwError $ err400 {errBody = BSL.pack . show $ e}

runFunction :: Evaluation -> Handler Blockchain
runFunction e = do
  mLibDir <- liftIO $ lookupEnv "GHC_LIB_DIR"
  r <- liftIO $ runInterpreter $ PI.runFunction e
  case r of
    Left e           -> throwError $ err400 {errBody = BSL.pack . show $ e}
    Right blockchain -> pure blockchain

handlers :: Server API
handlers = acceptSourceCode :<|> runFunction
