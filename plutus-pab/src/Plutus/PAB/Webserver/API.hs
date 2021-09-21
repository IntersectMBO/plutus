{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE TypeFamilies       #-}
{-# LANGUAGE TypeOperators      #-}

module Plutus.PAB.Webserver.API
    ( API
    , WSAPI
    , WalletProxy
    , SwaggerAPI
    ) where

import qualified Cardano.Wallet.Mock.API    as Wallet
import qualified Data.Aeson                 as JSON
import           Data.Text                  (Text)
import           Plutus.PAB.Webserver.Types (ContractActivationArgs, ContractInstanceClientState,
                                             ContractSignatureResponse, FullReport)
import           Servant.API                (Capture, Description, Get, JSON, Post, Put, ReqBody, (:<|>), (:>))
import           Servant.API.WebSocket      (WebSocketPending)
import           Servant.Swagger.UI         (SwaggerSchemaUI)
import           Wallet.Types               (ContractInstanceId)

type WalletProxy walletId = "wallet" :> (Wallet.API walletId)

type WSAPI =
    "ws" :>
        (Capture "contract-instance-id" ContractInstanceId :> WebSocketPending -- Websocket for a specific contract instance
        :<|> WebSocketPending -- Combined websocket (subscription protocol)
        )

-- | PAB client API for contracts of type @t@. An example of @t@ are
--   * "Builtin" contracts that run in the same process as the PAB (ie. the PAB is compiled & distributed with these contracts)
type API t walletId -- see note [WalletID type in wallet API]
    = "api" :> ("healthcheck" :> Description "Is the server alive?" :> Get '[JSON] ()
    :<|> ("fullreport" :> Description "Details of the contracts: the signatures and their states." :> Get '[JSON] (FullReport t))
    :<|> "contract" :> ("activate" :> ReqBody '[JSON] (ContractActivationArgs t) :> Description "Start a new instance." :> Post '[JSON] ContractInstanceId
            :<|> "instance" :>
                    (Capture "contract-instance-id" Text :>
                        (    "status"   :> Description "Current status of contract instance." :> Get '[JSON] (ContractInstanceClientState t)
                        :<|> "schema"   :> Description "Endpoints' schema of contract instance." :> Get '[JSON] (ContractSignatureResponse t)
                        :<|> "endpoint" :> Capture "endpoint-name" String :> ReqBody '[JSON] JSON.Value :> Description "Call an endpoint." :> Post '[JSON] ()
                        :<|> "stop"     :> Description "Terminate the instance." :> Put '[JSON] ()
                        )
                    )
            :<|> "instances" :> "wallet" :> Capture "wallet-id" walletId :> Description "List of all active contract instances for the wallet." :>  Get '[JSON] [ContractInstanceClientState t]
            :<|> "instances" :> Description "List of all active contract instances." :> Get '[JSON] [ContractInstanceClientState t]
            :<|> "definitions" :> Description "list of available contracts." :> Get '[JSON] [ContractSignatureResponse t]
        )
      )

type SwaggerAPI = "swagger" :> SwaggerSchemaUI "swagger-ui" "swagger.json"
