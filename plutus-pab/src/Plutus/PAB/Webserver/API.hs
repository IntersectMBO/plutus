{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE TypeFamilies       #-}
{-# LANGUAGE TypeOperators      #-}

module Plutus.PAB.Webserver.API
    ( API
    , WSAPI
    , WalletProxy
    ) where

import qualified Cardano.Wallet.API         as Wallet
import qualified Data.Aeson                 as JSON
import           Data.Text                  (Text)
import           Plutus.PAB.Webserver.Types (ContractActivationArgs, ContractInstanceClientState,
                                             ContractSignatureResponse, FullReport)
import           Servant.API                (Capture, Get, JSON, Post, Put, ReqBody, (:<|>), (:>))
import           Servant.API.WebSocket      (WebSocketPending)
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
    = "api" :> ("healthcheck" :> Get '[JSON] () -- Is the server alive?
    :<|> ("fullreport" :> Get '[JSON] (FullReport t)) -- Details of the contracts: the signatures and their states.
    :<|> "contract" :> ("activate" :> ReqBody '[JSON] (ContractActivationArgs t) :> Post '[JSON] ContractInstanceId -- Start a new instance.
            :<|> "instance" :>
                    (Capture "contract-instance-id" Text :>
                        (    "status"   :> Get '[JSON] (ContractInstanceClientState t) -- Current status of contract instance.
                        :<|> "schema"   :> Get '[JSON] (ContractSignatureResponse t)
                        :<|> "endpoint" :> Capture "endpoint-name" String :> ReqBody '[JSON] JSON.Value :> Post '[JSON] () -- Call an endpoint.
                        :<|> "stop"     :> Put '[JSON] () -- Terminate the instance.
                        )
                    )
            :<|> "instances" :> "wallet" :> Capture "wallet-id" walletId :> Get '[JSON] [ContractInstanceClientState t]
            :<|> "instances" :> Get '[JSON] [ContractInstanceClientState t] -- list of all active contract instances.
            :<|> "definitions" :> Get '[JSON] [ContractSignatureResponse t] -- list of available contracts.
        )
      )
