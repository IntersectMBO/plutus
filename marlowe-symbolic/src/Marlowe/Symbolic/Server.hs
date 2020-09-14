{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns        #-}
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
                                                        TransactionWarning, defaultMarloweFFIInfo)
import           Language.Marlowe.Analysis.FSSemantics (AnalysisResult (..), CounterExample (..), warningsTraceCustom)
import           Marlowe.Symbolic.Types.Request        (Request (..))
import qualified Marlowe.Symbolic.Types.Request        as Req
import           Marlowe.Symbolic.Types.Response       (Result (Error, Valid))
import qualified Marlowe.Symbolic.Types.Response       as Res
import           Servant                               ((:<|>) ((:<|>)), (:>), Application, Handler (Handler), JSON,
                                                        Post, ReqBody, Server, ServerError, hoistServer, serve)
import           System.Process                        (system)
import           Text.PrettyPrint.Leijen               (displayS, renderCompact)

type API = "marlowe-analysis" :> ReqBody '[JSON] Request :> Post '[JSON] Result

makeResponse :: Either String AnalysisResult -> Result
makeResponse result = case result of
    Left err -> Error err
    Right (AnalysisError err) -> Error (show err)
    Right (CounterExample MkCounterExample{ceInitialSlot=(Slot sn), ceTransactionInputs, ceWarnings}) ->
        Res.CounterExample
                       { Res.initialSlot = sn
                       , Res.transactionList = ceTransactionInputs
                       , Res.transactionWarning = ceWarnings
                       }
    Right ValidContract -> Valid

handlers :: Server API
handlers Request {..} =
  liftIO $ do
    _ <- system "killallz3"
    -- FIXME pass MarloweFFIInfo here instead of defaultMarloweFFI
    evRes <- warningsTraceCustom defaultMarloweFFIInfo onlyAssertions contract (Just state)
    let resp = makeResponse (Right evRes)
    _ <- system "killallz3"
    putStrLn $ BSU.toString $ JSON.encode resp
    pure resp

app :: Application
app = serve (Proxy @API) handlers

initializeContext :: IO ()
initializeContext = pure ()

initializeApplication :: IO Application
initializeApplication = pure app
