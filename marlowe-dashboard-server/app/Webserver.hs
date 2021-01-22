{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}

module Webserver where

import           API                      (API)
import           Data.Proxy               (Proxy (Proxy))
import           Network.Wai.Handler.Warp as Warp
import           Servant                  (serve)
import qualified Server

run :: Int -> IO ()
run port = do
  let server = Server.handlers
  Warp.run port (serve (Proxy @API) server)
