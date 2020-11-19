{-# LANGUAGE DataKinds     #-}
{-# LANGUAGE TypeOperators #-}

module Plutus.SCB.Swagger
    ( SwaggerAPI
    , module X
    , handler
    ) where

import           Data.Proxy      (Proxy)
import           Data.Swagger    (Swagger, ToSchema, declareNamedSchema)
import qualified Data.Swagger    as X
import           Servant         (Handler)
import           Servant.API     (Get, JSON, (:>))
import           Servant.Swagger (HasSwagger, toSwagger)

type SwaggerAPI = "swagger.json" :> Get '[ JSON] Swagger

handler :: HasSwagger api => Proxy api -> Handler Swagger
handler = pure . toSwagger
