module Playground.Server where

import           Control.Monad.IO.Class       (liftIO)
import qualified Data.ByteString.Lazy.Char8   as BSL
import           Language.Haskell.Interpreter (runInterpreter)
import           Playground.API               (API, Evaluation, FunctionSchema, FunctionsSchema (FunctionsSchema),
                                               SourceCode)
import qualified Playground.Interpreter       as Interpreter
import           Servant                      (err400, errBody, throwError)
import           Servant.API                  ((:<|>) ((:<|>)), NoContent (NoContent))
import           Servant.Server               (Handler, Server)
import           Wallet.UTXO.Types            (Blockchain)

acceptSourceCode :: SourceCode -> Handler [FunctionSchema]
acceptSourceCode sourceCode = do
  r <- liftIO $ runInterpreter $ Interpreter.compile sourceCode
  liftIO . print $ r
  case r of
    Left e  -> throwError $ err400 {errBody = BSL.pack . show $ e}
    Right v -> pure v

runFunction :: Evaluation -> Handler Blockchain
runFunction e = do
  r <- liftIO $ runInterpreter $ Interpreter.runFunction e
  liftIO . print $ r
  case r of
    Left e           -> throwError $ err400 {errBody = BSL.pack . show $ e}
    Right blockchain -> pure blockchain

handlers :: Server API
handlers = acceptSourceCode :<|> runFunction
