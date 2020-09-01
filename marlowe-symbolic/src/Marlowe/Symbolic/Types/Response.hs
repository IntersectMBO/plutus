{-# LANGUAGE DeriveGeneric #-}
module Marlowe.Symbolic.Types.Response where

import           Data.Aeson   (FromJSON, ToJSON)
import           GHC.Generics

data Result = Valid
            | CounterExample
                { initialSlot        :: Integer
                , transactionList    :: String
                , transactionWarning :: String
                }
            | Error String
  deriving (Generic)
instance FromJSON Result
instance ToJSON Result
