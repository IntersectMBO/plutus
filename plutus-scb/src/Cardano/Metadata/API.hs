{-# LANGUAGE DataKinds     #-}
{-# LANGUAGE TypeOperators #-}

module Cardano.Metadata.API
    ( API
    ) where

import           Cardano.Metadata.Types (Property, PropertyKey, Subject)
import           Servant.API            ((:<|>), (:>), Capture, Get, JSON)

type API
     = "metadata" :> Capture "subject" Subject :> ("properties" :> Get '[ JSON] [Property]
                                                   :<|> "property" :> Capture "property" PropertyKey :> Get '[ JSON] Property)
