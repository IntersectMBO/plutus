module Template.Types
  ( Template
  ) where

import Marlowe.Extended (Contract)

type Template
  = { name :: String
    , type_ :: String
    , description :: String
    , contract :: Contract
    }
