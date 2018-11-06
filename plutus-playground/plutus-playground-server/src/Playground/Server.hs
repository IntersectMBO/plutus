module Playground.Server
  ( handlers
  ) where

import           Control.Monad.IO.Class       (liftIO)
import           Data.Aeson                   (encode)
import qualified Data.ByteString.Lazy.Char8   as BSL
import           Data.Maybe                   (catMaybes, fromMaybe)
import qualified Data.Text                    as Text
import           Language.Haskell.Interpreter (InterpreterError (WontCompile), errMsg, runInterpreter)
import           Playground.API               (API, CompilationError, Evaluation, FunctionSchema,
                                               FunctionsSchema (FunctionsSchema), SourceCode, parseErrorText)
import qualified Playground.Interpreter       as Interpreter
import           Servant                      (err400, errBody, throwError)
import           Servant.API                  ((:<|>) ((:<|>)), NoContent (NoContent))
import           Servant.Server               (Handler, Server)
import           Wallet.UTXO.Types            (Blockchain)

acceptSourceCode ::
     SourceCode -> Handler (Either [CompilationError] [FunctionSchema])
acceptSourceCode sourceCode = do
  r <- liftIO $ runInterpreter $ Interpreter.compile sourceCode
  case r of
    Right v -> pure (Right v)
    Left (WontCompile errors) ->
      pure $ Left $ map (parseErrorText . Text.pack . errMsg) errors
    Left e -> throwError $ err400 {errBody = BSL.pack . show $ e}

runFunction :: Evaluation -> Handler Blockchain
runFunction e = do
  r <- liftIO $ runInterpreter $ Interpreter.runFunction e
  case r of
    Left e           -> throwError $ err400 {errBody = BSL.pack . show $ e}
    Right blockchain -> pure blockchain

handlers :: Server API
handlers = acceptSourceCode :<|> runFunction
