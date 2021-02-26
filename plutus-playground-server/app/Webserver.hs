{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}

module Webserver where

import           Data.Proxy               (Proxy (Proxy))
import           Network.Wai.Handler.Warp as Warp
import           Playground.Server        (initializeServerContext)
import qualified Playground.Server        as Server
import           Servant                  (serve, (:<|>) ((:<|>)))
import qualified Webghc.Server            as Webghc

type API = Server.Web :<|> Webghc.API

run :: Int -> Maybe FilePath -> IO ()
run port secrets = do
  appConfig <- initializeServerContext secrets
  handlers <- Server.mkHandlers appConfig
  let server = handlers :<|> Webghc.server
  Warp.run port (serve (Proxy @API) server)
