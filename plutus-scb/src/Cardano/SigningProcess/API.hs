{-# LANGUAGE DataKinds     #-}
{-# LANGUAGE TypeOperators #-}

module Cardano.SigningProcess.API
    ( API
    ) where

import           Ledger      (PubKeyHash, Tx)
import           Servant.API (Get, JSON, ReqBody, (:>))

type API = "add-signatures" :> ReqBody '[ JSON] ([PubKeyHash], Tx) :> Get '[ JSON] Tx
