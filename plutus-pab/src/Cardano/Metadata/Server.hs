{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE NamedFieldPuns    #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes        #-}
{-# LANGUAGE TypeApplications  #-}
{-# LANGUAGE TypeFamilies      #-}
{-# LANGUAGE TypeOperators     #-}

module Cardano.Metadata.Server
    ( main
    , handleMetadata
    ) where

import           Control.Monad.Except             (ExceptT (ExceptT))
import           Control.Monad.Freer              (Eff, Member, interpret, runM)
import           Control.Monad.Freer.Error        (Error, runError)
import           Control.Monad.IO.Class           (liftIO)
import           Data.Bifunctor                   (first)
import qualified Data.ByteString.Lazy.Char8       as BSL
import           Data.Function                    ((&))
import           Data.Proxy                       (Proxy (Proxy))
import qualified Network.Wai.Handler.Warp         as Warp
import           Servant                          (Application, Handler (Handler), ServerError, err404, err500, errBody,
                                                   hoistServer, serve)
import           Servant.API                      ((:<|>) ((:<|>)))
import           Servant.Client                   (baseUrlPort)


import           Cardano.BM.Data.Trace            (Trace)
import           Cardano.Metadata.API             (API)
import           Cardano.Metadata.Mock
import           Cardano.Metadata.Types
import           Control.Concurrent.Availability  (Availability, available)
import           Control.Monad.Freer.Extras.Log   (LogMsg, logInfo)
import           Data.Coerce                      (coerce)
import qualified Plutus.PAB.Monitoring.Monitoring as LM

handler ::
       Member MetadataEffect effs
    => (Subject -> (Eff effs (SubjectProperties 'AesonEncoding)
                    :<|> (PropertyKey -> Eff effs (Property 'AesonEncoding))))
       :<|> (Query -> Eff effs (QueryResult 'AesonEncoding))
handler =
    (\subject -> getProperties subject :<|> getProperty subject) :<|> batchQuery

asHandler ::
    Trace IO MetadataLogMessage
    -> Eff '[ MetadataEffect, LogMsg MetadataLogMessage, Error MetadataError, IO] a
    -> Handler a
asHandler trace =
    Handler .
    ExceptT .
    runM .
    fmap (first toServerError) . runError . interpret (LM.handleLogMsgTrace trace) . handleMetadata

toServerError :: MetadataError -> ServerError
toServerError err@(SubjectNotFound _) = err404 {errBody = BSL.pack $ show err}
toServerError err@(SubjectPropertyNotFound _ _) =
    err404 {errBody = BSL.pack $ show err}
toServerError err@(MetadataClientError _) =
    err500 {errBody = BSL.pack $ show err}

app :: Trace IO MetadataLogMessage -> Application
app trace = serve api apiServer
  where
    api = Proxy @(API 'AesonEncoding)
    apiServer = hoistServer api (asHandler trace) handler

main :: Trace IO MetadataLogMessage -> MetadataConfig ->  Availability -> IO ()
main trace MetadataConfig {mdBaseUrl} availability = LM.runLogEffects trace $ do
    logInfo $ StartingMetadataServer port
    liftIO $ Warp.runSettings warpSettings (app trace)
        where
            port = baseUrlPort (coerce mdBaseUrl)
            warpSettings = Warp.defaultSettings &
                Warp.setPort port &
                Warp.setBeforeMainLoop (available availability)
