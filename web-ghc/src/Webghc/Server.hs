{-# LANGUAGE DataKinds     #-}
{-# LANGUAGE TypeOperators #-}
module Webghc.Server where

import           Control.Monad.Catch          (MonadMask)
import           Control.Monad.Except         (runExceptT)
import           Control.Monad.IO.Class       (MonadIO, liftIO)
import           Data.Text                    (Text)
import           Git                          (gitRev)
import           Interpreter                  (compile, maxInterpretationTime)
import           Language.Haskell.Interpreter (InterpreterError, InterpreterResult)
import           Language.Haskell.Interpreter (SourceCode (SourceCode))
import           Servant                      ((:<|>) ((:<|>)), (:>), Get, JSON, PlainText, Post, QueryFlag, ReqBody)
import           Servant.Server               (Server)

type API =
  "version" :> Get '[PlainText, JSON] Text
    :<|> "health" :> Get '[JSON] ()
    :<|> "runghc" :> QueryFlag "prelude" :> ReqBody '[PlainText] Text :> Post '[JSON] (Either InterpreterError (InterpreterResult String))

server :: Server API
server =
  version :<|> health :<|> runghc

version :: Applicative m => m Text
version = pure gitRev

health :: Applicative m => m ()
health = pure ()

runghc ::
  MonadMask m =>
  MonadIO m =>
  Bool ->
  Text ->
  m (Either InterpreterError (InterpreterResult String))
runghc implicitPrelude code = do
  liftIO $ print code
  runExceptT $ compile maxInterpretationTime implicitPrelude $ SourceCode code
