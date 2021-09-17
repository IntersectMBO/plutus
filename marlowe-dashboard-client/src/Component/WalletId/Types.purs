module Component.WalletId.Types (Input) where

import Marlowe.PAB (PlutusAppId)

type Input
  = { inputId :: String
    , label :: String
    , value :: PlutusAppId
    }
