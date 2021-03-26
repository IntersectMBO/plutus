{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE TypeFamilies       #-}
{-# LANGUAGE TypeOperators      #-}

module Plutus.PAB.Webserver.API
    ( API
    , WSAPI
    , WalletProxy
    -- * New API that will eventually replace 'API'
    , NewAPI
    ) where

import qualified Cardano.Wallet.API         as Wallet
import qualified Data.Aeson                 as JSON
import           Data.Text                  (Text)
import           Plutus.PAB.Webserver.Types (ContractActivationArgs, ContractInstanceClientState,
                                             ContractSignatureResponse, FullReport)
import           Servant.API                (Capture, Get, JSON, Post, ReqBody, (:<|>), (:>))
import           Servant.API.WebSocket      (WebSocketPending)
import           Wallet.Types               (ContractInstanceId, NotificationError)

type WalletProxy = "wallet" :> Wallet.API

type API t
     = "api" :> ("healthcheck" :> Get '[ JSON] ()
                 :<|> "full-report" :> Get '[ JSON] (FullReport t)
                 :<|> "contract" :> ("activate" :> ReqBody '[ JSON] t :> Post '[ JSON] ContractInstanceId
                                     :<|> Capture "contract-instance-id" Text :> ("schema" :> Get '[ JSON] (ContractSignatureResponse t)
                                                                                  :<|> "endpoint" :> Capture "endpoint-name" String :> ReqBody '[ JSON] JSON.Value :> Post '[JSON] (Maybe NotificationError))))

type WSAPI =
    "ws" :>
        (Capture "contract-instance-id" ContractInstanceId :> WebSocketPending -- ^ Websocket for a specific contract instance
        :<|> WebSocketPending -- ^ Combined websocket (subscription protocol)
        )

-- | PAB client API for contracts of type @t@. Examples of @t@ are
--   * Contract executables that reside in the user's file system
--   * "Builtin" contracts that run in the same process as the PAB (ie. the PAB is compiled & distributed with these contracts)
type NewAPI t
    = "api" :> "new" :> "contract" :>
        ("activate" :> ReqBody '[ JSON] (ContractActivationArgs t) :> Post '[JSON] ContractInstanceId -- start a new instance
            :<|> "instance" :>
                    (Capture "contract-instance-id" Text :>
                        ( "status" :> Get '[JSON] (ContractInstanceClientState) -- ^ Current status of contract instance
                        :<|> "endpoint" :> Capture "endpoint-name" String :> ReqBody '[JSON] JSON.Value :> Post '[JSON] () -- ^ Call an endpoint. Make
                        )
                    )
            :<|> "instances" :> "wallet" :> Capture "wallet-id" Integer :> Get '[JSON] [ContractInstanceClientState]
            :<|> "instances" :> Get '[ JSON] [ContractInstanceClientState] -- list of all active contract instances
            :<|> "definitions" :> Get '[JSON] [ContractSignatureResponse t] -- list of available contracts
        )
