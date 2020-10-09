{-# LANGUAGE DeriveGeneric #-}
module Marlowe.Symbolic.Types.Request where

import           Data.Aeson       (FromJSON, ToJSON)
import           GHC.Generics     (Generic)
import           Language.Marlowe (Contract, State)

data Request = Request
  { onlyAssertions :: Bool
  , contract       :: Contract
  , state          :: State
  } deriving (Generic)
instance FromJSON Request
instance ToJSON Request

