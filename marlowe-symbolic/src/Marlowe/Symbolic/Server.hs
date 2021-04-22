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

import           Control.Exception                     (evaluate)
import           Control.Monad.IO.Class                (MonadIO, liftIO)
import qualified Data.Aeson                            as JSON
import           Data.Bifunctor                        (first)
import           Data.ByteString.Lazy.UTF8             as BSU
import           Data.Maybe                            (fromMaybe)
import           Data.Proxy                            (Proxy (Proxy))
import           Formatting                            (fprintLn, (%))
import           Formatting.Clock                      (timeSpecs)
import           Language.Marlowe                      (Contract, Slot (Slot), State, TransactionInput,
                                                        TransactionWarning)
import           Language.Marlowe.Analysis.FSSemantics (warningsTraceCustom)
import           Marlowe.Symbolic.Types.Request        (Request (..))
import           Marlowe.Symbolic.Types.Response       (Response (..), Result (..))
import           Servant                               (Application, Handler (Handler), JSON, Post, ReqBody, Server,
                                                        ServerError, hoistServer, serve, (:<|>) ((:<|>)), (:>))
import           System.Clock                          (Clock (Monotonic), diffTimeSpec, getTime, toNanoSecs)
import           System.Process                        (system)
import           Text.PrettyPrint.Leijen               (displayS, renderCompact)

type API = "marlowe-analysis" :> ReqBody '[JSON] Request :> Post '[JSON] Response

makeResult ::
  Either String (Maybe (Slot, [TransactionInput], [TransactionWarning])) ->
  Result
makeResult (Left err) = Error (show err)
makeResult (Right res) =
  case res of
        Nothing -> Valid
        Just (Slot sn, ti, tw) ->
          CounterExample
            { initialSlot = sn
            , transactionList = ti
            , transactionWarning = tw
            }

handlers :: Server API
handlers Request {..} =
  liftIO $ do
    start <- getTime Monotonic
    evRes <- warningsTraceCustom onlyAssertions contract (Just state)
    evaluate evRes
    end <- getTime Monotonic
    let res = Response { result = makeResult (first show evRes)
                       , durationMs = (toNanoSecs $ diffTimeSpec start end) `div` 1000000
                       }
    putStrLn $ BSU.toString $ JSON.encode res
    fprintLn ("Static analysis took " % timeSpecs) start end
    pure res

app :: Application
app = serve (Proxy @API) handlers

initializeContext :: IO ()
initializeContext = pure ()

initializeApplication :: IO Application
initializeApplication = pure app

