{-# LANGUAGE DataKinds     #-}
{-# LANGUAGE TypeOperators #-}

module Plutus.SCB.Webserver.API
    ( API
    ) where

import qualified Data.Aeson                 as JSON
import           Data.Text                  (Text)
import           Plutus.SCB.Webserver.Types (ContractSignatureResponse, FullReport)
import           Servant.API                ((:<|>), (:>), Capture, Get, JSON, Put, ReqBody)

type API t
     = "healthcheck" :> Get '[ JSON] ()
       :<|> "full-report" :> Get '[ JSON] (FullReport t)
       :<|> "contract" :> Capture "contract-instance-id" Text :> ("schema" :> Get '[ JSON] (ContractSignatureResponse t)
                                                                  :<|> "endpoint" :> Capture "endpoint-name" String :> ReqBody '[ JSON] JSON.Value :> Put '[ JSON] (ContractSignatureResponse t))
