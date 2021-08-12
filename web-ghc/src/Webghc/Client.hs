{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeApplications #-}
module Webghc.Client where

import           Control.Monad.Error.Class    (MonadError, throwError)
import           Control.Monad.IO.Class       (MonadIO, liftIO)
import           Data.Proxy                   (Proxy (Proxy))
import qualified Data.Text                    as Text
import           Language.Haskell.Interpreter (CompilationError (RawError), InterpreterError (CompilationErrors),
                                               InterpreterResult)
import           Servant.Client               (ClientEnv, ClientM, client, runClientM)
import           Webghc.Server                (CompileRequest, FrontendAPI)

runghc :: CompileRequest -> ClientM (Either InterpreterError (InterpreterResult String))
runghc = client (Proxy @FrontendAPI)

-- | Run a script using a webghc backend specified in the client environment
runscript ::
  ( MonadIO m,
    MonadError InterpreterError m
  ) =>
  ClientEnv ->
  CompileRequest ->
  m (InterpreterResult String)
runscript clientEnv code = do
  res <- liftIO $ flip runClientM clientEnv $ runghc $ code
  case res of
    Left e          -> throwError (CompilationErrors [RawError (Text.pack (show e))])
    Right (Left e)  -> throwError e
    Right (Right r) -> pure r
