{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE TypeFamilies       #-}
{-# LANGUAGE TypeOperators      #-}

module Plutus.PAB.Webserver.API
    ( API
    , WSAPI
    -- * New API that will eventually replace 'API'
    , NewAPI
    , ContractActivationArgs(..)
    , WalletInfo(..)
    , ContractInstanceClientState(..)
    ) where

import qualified Data.Aeson                                      as JSON
import           Data.Text                                       (Text)
import           GHC.Generics                                    (Generic)
import           Plutus.Contract.Effects.ExposeEndpoint (ActiveEndpoint)
import           Plutus.PAB.Events.ContractInstanceState         (PartiallyDecodedResponse)

import           Plutus.PAB.Webserver.Types                      (ContractSignatureResponse, FullReport)
import           Servant.API                                     (Capture, Get, JSON, Post, ReqBody, (:<|>), (:>))
import           Servant.API.WebSocket                           (WebSocketPending)
import           Wallet.Emulator.Wallet                          (Wallet)
import           Wallet.Types                                    (ContractInstanceId, NotificationError)

type API t
     = "api" :> ("healthcheck" :> Get '[ JSON] ()
                 :<|> "full-report" :> Get '[ JSON] (FullReport t)
                 :<|> "contract" :> ("activate" :> ReqBody '[ JSON] t :> Post '[ JSON] ContractInstanceId
                                     :<|> Capture "contract-instance-id" Text :> ("schema" :> Get '[ JSON] (ContractSignatureResponse t)
                                                                                  :<|> "endpoint" :> Capture "endpoint-name" String :> ReqBody '[ JSON] JSON.Value :> Post '[JSON] (Maybe NotificationError))))

type WSAPI = "ws" :> WebSocketPending

-- | Describes the wallet that should be used for the contract instance. 'Wallet' is a placeholder, we probably need a URL or some other data.
newtype WalletInfo = WalletInfo { unWalletInfo :: Wallet }
    deriving stock (Eq, Show, Generic)
    deriving anyclass (JSON.ToJSON, JSON.FromJSON)

-- | Data needed to start a new instance of a contract.
data ContractActivationArgs t =
    ContractActivationArgs
        { caID     :: t -- ^ ID of the contract
        , caWallet :: WalletInfo -- ^ Wallet that should be used for this instance
        }
    deriving stock (Eq, Show, Generic)
    deriving anyclass (JSON.ToJSON, JSON.FromJSON)

-- | Current state of a contract instance
--   (to be sent to external clients)
data ContractInstanceClientState =
    ContractInstanceClientState
        { cicContract     :: ContractInstanceId
        , cicCurrentState :: PartiallyDecodedResponse ActiveEndpoint
        }
        deriving stock (Eq, Show, Generic)
        deriving anyclass (JSON.ToJSON, JSON.FromJSON)

-- | PAB client API for contracts of type @t@. Examples of @t@ are
--   * Contract executables that reside in the user's file system
--   * "Builtin" contracts that run in the same process as the PAB (ie. the PAB is compiled & distributed with these contracts)
type NewAPI t
    = "api" :> "new" :> "contract" :>
        ("activate" :> ReqBody '[ JSON] (ContractActivationArgs t) :> Post '[JSON] ContractInstanceId -- start a new instance
            :<|> "instance" :>
                    (Capture "contract-instance-id" ContractInstanceId :>
                        ( "status" :> Get '[JSON] (ContractInstanceClientState) -- ^ Current status of contract instance
                        :<|> "endpoint" :> Capture "endpoint-name" String :> ReqBody '[JSON] JSON.Value :> Post '[JSON] () -- ^ Call an endpoint. Make
                        :<|> "ws" :> WebSocketPending -- status updates, incl. open endpoints, for contract instance
                        )
                    )
            :<|> "instances" :> Get '[ JSON] [ContractInstanceClientState] -- list of all active contract instances
            :<|> "definitions" :> Get '[JSON] [ContractSignatureResponse t] -- list of available contracts
        )
