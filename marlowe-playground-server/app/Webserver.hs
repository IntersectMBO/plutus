{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}

module Webserver where

import           Data.Proxy               (Proxy (Proxy))
import qualified Marlowe.Symbolic.Server  as MS
import           Network.Wai.Handler.Warp as Warp
import           Servant                  ((:<|>) ((:<|>)), serve)
import           Server                   (initializeContext)
import qualified Server
import qualified Webghc.Server            as Webghc

type API = Server.Web :<|> Webghc.API :<|> MS.API

run :: Int -> IO ()
run port = do
  appConfig <- initializeContext
  handlers <- Server.mkHandlers appConfig
  let server = handlers :<|> Webghc.server :<|> MS.handlers
  Warp.run port (serve (Proxy @API) server)
