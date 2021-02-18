module Template.Types
  ( Template
  , Contract
  ) where

type Template
  = { name :: String
    , type_ :: String
    , description :: String
    , contract :: Contract
    }

-- TODO: move Marlowe.Extended to web-common-marlowe and import Marlowe.Extended.Contract
type Contract
  = Int
