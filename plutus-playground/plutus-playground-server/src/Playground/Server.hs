module Playground.Server where

import           Control.Monad.IO.Class       (liftIO)
import qualified Data.ByteString.Lazy.Char8   as BSL
import           Language.Haskell.Interpreter (runInterpreter)
import           Playground.API               (FunctionsSchema(FunctionsSchema), API, Evaluation, SourceCode, contract, program)
import qualified Playground.Interpreter       as Interpreter
import           Servant                      (err400, errBody, throwError)
import           Servant.API                  ((:<|>) ((:<|>)), NoContent (NoContent))
import           Servant.Server               (Handler, Server)
import           Wallet.UTXO.Types            (Blockchain)

acceptSourceCode :: SourceCode -> Handler FunctionsSchema
acceptSourceCode sourceCode = do
  r <- liftIO $ runInterpreter $ Interpreter.compile sourceCode
  liftIO . print $ r
  case r of
    Left e  -> throwError $ err400 {errBody = BSL.pack . show $ e}
    Right _ -> pure $ FunctionsSchema []

runFunction :: Evaluation -> Handler Blockchain
runFunction e = do
  let sourceCode = contract e
  r <- liftIO $ runInterpreter $ Interpreter.runFunction sourceCode $ program e
  liftIO . print $ r
  case r of
    Left e  -> throwError $ err400 {errBody = BSL.pack . show $ e}
    Right _ -> pure []

handlers :: Server API
handlers = acceptSourceCode :<|> runFunction
