{-# LANGUAGE DataKinds     #-}
{-# LANGUAGE TypeOperators #-}

module Cardano.Protocol.Socket.Mock.API where

import Servant.API ((:>), Get, JSON, NoContent)

type API = "addBlock" :> Get '[ JSON] NoContent
