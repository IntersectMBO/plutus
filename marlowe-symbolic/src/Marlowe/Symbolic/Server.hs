{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE RecordWildCards       #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeOperators         #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Marlowe.Symbolic.Server where

import           Control.Monad.IO.Class                (MonadIO, liftIO)
import qualified Data.Aeson                            as JSON
import           Data.Bifunctor                        (first)
import           Data.ByteString.Lazy.UTF8             as BSU
import           Data.Maybe                            (fromMaybe)
import           Data.Proxy                            (Proxy (Proxy))
import           Language.Marlowe                      (Contract, Slot (Slot), State, TransactionInput,
                                                        TransactionWarning)
import           Language.Marlowe.Analysis.FSSemantics (warningsTraceCustom)
import           Marlowe.Symbolic.Types.Request        (Request (..))
import           Marlowe.Symbolic.Types.Response       (Result (..))
import           Servant                               (Application, Handler (Handler), JSON, Post, ReqBody, Server,
                                                        ServerError, hoistServer, serve, (:<|>) ((:<|>)), (:>))
import           System.Process                        (system)
import           Text.PrettyPrint.Leijen               (displayS, renderCompact)

type API = "marlowe-analysis" :> ReqBody '[JSON] Request :> Post '[JSON] Result

makeResponse ::
  Either String (Maybe (Slot, [TransactionInput], [TransactionWarning])) ->
  Result
makeResponse (Left err) = Error (show err)
makeResponse (Right res) =
  case res of
        Nothing -> Valid
        Just (Slot sn, ti, tw) ->
          CounterExample
            { initialSlot = sn,
              transactionList = ti,
              transactionWarning = tw
            }

handlers :: Server API
handlers Request {..} =
  liftIO $ do
    _ <- system "killallz3"
    evRes <- warningsTraceCustom onlyAssertions contract (Just state)
    let resp = makeResponse (first show evRes)
    _ <- system "killallz3"
    putStrLn $ BSU.toString $ JSON.encode resp
    pure resp

app :: Application
app = serve (Proxy @API) handlers

initializeContext :: IO ()
initializeContext = pure ()

initializeApplication :: IO Application
initializeApplication = pure app
