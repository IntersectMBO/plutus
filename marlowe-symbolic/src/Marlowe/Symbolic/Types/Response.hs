{-# LANGUAGE DeriveGeneric #-}
module Marlowe.Symbolic.Types.Response where

import           Data.Aeson                 (FromJSON, ToJSON)
import           GHC.Generics
import           Language.Marlowe.Semantics (TransactionInput, TransactionWarning)

data Result = Valid
            | CounterExample
                { initialSlot        :: Integer
                , transactionList    :: [TransactionInput]
                , transactionWarning :: [TransactionWarning]
                }
            | Error String
  deriving (Generic)

instance FromJSON Result
instance ToJSON Result

data Response = Response { result     :: Result
                         , durationMs :: Integer
                         }
  deriving (Generic)

instance FromJSON Response
instance ToJSON Response


