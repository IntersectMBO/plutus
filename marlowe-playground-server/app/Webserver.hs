{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}

module Webserver where

import           Data.Proxy               (Proxy (Proxy))
import           Data.Time.Units          (Second)
import qualified Marlowe.Symbolic.Server  as MS
import           Network.Wai.Handler.Warp as Warp
import           Servant                  (serve, (:<|>) ((:<|>)))
import           Server                   (initializeServerContext)
import qualified Server
import qualified Webghc.Server            as Webghc

type API = Server.Web :<|> Webghc.API :<|> MS.API

run :: Int -> Second -> Maybe FilePath ->  IO ()
run port maxInterpretationTime secrets = do
  appConfig <- initializeServerContext maxInterpretationTime secrets
  handlers <- Server.mkHandlers appConfig
  let server = handlers :<|> Webghc.server 80 :<|> MS.handlers
  Warp.run port (serve (Proxy @API) server)
