{-# LANGUAGE DataKinds     #-}
{-# LANGUAGE TypeFamilies  #-}
{-# LANGUAGE TypeOperators #-}

module Plutus.PAB.Webserver.API
    ( API
    , WSAPI
    , DocumentationAPI
    -- * New API that will eventually replace 'API'
    , NewAPI
    , ContractActivationArgs(..)
    , WalletInfo(..)
    ) where

import qualified Data.Aeson                              as JSON
import           Data.Text                               (Text)
import           Plutus.PAB.Events.ContractInstanceState (ContractInstanceState)
import           Plutus.PAB.Webserver.Types              (ContractSignatureResponse, FullReport)
import           Servant.API                             (Capture, Get, JSON, Post, ReqBody, (:<|>), (:>))
import           Servant.API.WebSocket                   (WebSocketPending)
import           Wallet.Emulator.Wallet                  (Wallet)

type API t
     = "api" :> ("healthcheck" :> Get '[ JSON] ()
                 :<|> "full-report" :> Get '[ JSON] (FullReport t)
                 :<|> "contract" :> ("activate" :> ReqBody '[ JSON] t :> Post '[ JSON] (ContractInstanceState t)
                                     :<|> Capture "contract-instance-id" Text :> ("schema" :> Get '[ JSON] (ContractSignatureResponse t)
                                                                                  :<|> "endpoint" :> Capture "endpoint-name" String :> ReqBody '[ JSON] JSON.Value :> Post '[ JSON] (ContractInstanceState t))))

type WSAPI = "ws" :> WebSocketPending

type DocumentationAPI t
     = "api" :> "healthcheck" :> Get '[ JSON] ()


type family ContractID t
type family InstanceID t

-- | Describes the wallet that should be used for the contract instance. 'Wallet' is a placeholder, we probably need a URL or some other data.
newtype WalletInfo = WalletInfo { unWalletInfo :: Wallet }

-- | Data needed to start a new instance of a contract.
data ContractActivationArgs t =
    ContractActivationArgs
        { caID     :: ContractID t -- ^ ID of the contract
        , caWallet :: WalletInfo -- ^ Wallet that should be used for this instance
        }

-- | PAB client API for contracts of type @t@. Examples of @t@ are
--   * Contract executables that reside in the user's file system
--   * "Builtin" contracts that run in the same process as the PAB (ie. the PAB is compiled & distributed with these contracts)
type NewAPI t
    = "contract" :>
        ("activate" :> ReqBody '[ JSON] (ContractActivationArgs t) :> Post '[JSON] (ContractInstanceState t) -- start a new instance
            :<|> "instance" :>
                    (Capture "instance-id" (InstanceID t) :> WebSocketPending -- status updates & endpoints for specific instance
                        :<|> Get '[ JSON] [ContractInstanceState t] -- list of all instances
                    )
            :<|> Get '[JSON] [ContractSignatureResponse t] -- list of available contracts
        )

