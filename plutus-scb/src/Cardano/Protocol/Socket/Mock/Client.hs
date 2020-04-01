{-# LANGUAGE TypeApplications #-}

module Cardano.Protocol.Socket.Mock.Client where

import Data.Proxy (Proxy (..))
import Servant (NoContent)
import Servant.Client (ClientM, client)

import Cardano.Protocol.Socket.Mock.API

addBlock :: ClientM NoContent
addBlock = client (Proxy @API)
