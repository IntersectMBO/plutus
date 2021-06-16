{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE RecordWildCards    #-}
{-# LANGUAGE TypeOperators      #-}
module Webghc.Server where

import           Control.Monad.Catch          (MonadMask)
import           Control.Monad.Except         (runExceptT)
import           Control.Monad.IO.Class       (MonadIO, liftIO)
import           Data.Aeson                   (FromJSON, ToJSON)
import           Data.Text                    (Text)
import           Data.Time.Units              (Second)
import           GHC.Generics                 (Generic)
import           Interpreter                  (compile)
import           Language.Haskell.Interpreter (InterpreterError, InterpreterResult, SourceCode (SourceCode))
import           Servant                      (Get, JSON, Post, ReqBody, (:<|>) ((:<|>)), (:>))
import           Servant.Server               (Server)

type FrontendAPI = "runghc" :> ReqBody '[JSON] CompileRequest :> Post '[JSON] (Either InterpreterError (InterpreterResult String))

type API =
  "health" :> Get '[JSON] ()
    :<|> FrontendAPI

data CompileRequest = CompileRequest { code :: Text, implicitPrelude :: Bool }
  deriving stock (Generic)
  deriving anyclass (FromJSON, ToJSON)

server :: Second -> Server API
server timeoutSecs =
  health :<|> runghc timeoutSecs

health :: Applicative m => m ()
health = pure ()

runghc ::
  MonadMask m =>
  MonadIO m =>
  Second ->
  CompileRequest ->
  m (Either InterpreterError (InterpreterResult String))
runghc timeoutSecs CompileRequest {..} = do
  liftIO $ print code
  runExceptT $ compile timeoutSecs implicitPrelude $ SourceCode code
