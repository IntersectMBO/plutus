{-# LANGUAGE TypeApplications #-}
module Cardano.SigningProcess.Client where

import           Cardano.SigningProcess.API (API)
import           Data.Proxy                 (Proxy (Proxy))
import           Ledger                     (PubKeyHash, Tx)
import           Servant.Client             (ClientM, client)

addSignatures :: [PubKeyHash] -> Tx -> ClientM Tx
addSignatures = curry addSignatures_ where
    addSignatures_ = client (Proxy @API)
