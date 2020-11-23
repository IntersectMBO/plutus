{-# LANGUAGE DataKinds     #-}
{-# LANGUAGE TypeOperators #-}

module Plutus.SCB.Webserver.API
    ( API
    , WSAPI
    , DocumentationAPI
    ) where

import qualified Data.Aeson                 as JSON
import           Data.Text                  (Text)
import           Plutus.SCB.Events          (ContractInstanceState)
import           Plutus.SCB.Webserver.Types (ContractSignatureResponse, FullReport)
import           Servant.API                (Capture, Get, JSON, Post, ReqBody, (:<|>), (:>))
import           Servant.API.WebSocket      (WebSocketPending)

type API t
     = "api" :> ("healthcheck" :> Get '[ JSON] ()
                 :<|> "full-report" :> Get '[ JSON] (FullReport t)
                 :<|> "contract" :> ("activate" :> ReqBody '[ JSON] t :> Post '[ JSON] (ContractInstanceState t)
                                     :<|> Capture "contract-instance-id" Text :> ("schema" :> Get '[ JSON] (ContractSignatureResponse t)
                                                                                  :<|> "endpoint" :> Capture "endpoint-name" String :> ReqBody '[ JSON] JSON.Value :> Post '[ JSON] (ContractInstanceState t))))

type WSAPI = "ws" :> WebSocketPending

type DocumentationAPI t
     = "api" :> "healthcheck" :> Get '[ JSON] ()
