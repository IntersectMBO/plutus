{-# LANGUAGE DeriveGeneric #-}
module Marlowe.Symbolic.Types.Request where

import           Data.Aeson
import           GHC.Generics

data Request = Request
  { uuid           :: String
  , callbackUrl    :: String
  , onlyAssertions :: String
  , contract       :: String
  , state          :: String
  } deriving (Generic)
instance FromJSON Request
instance ToJSON Request

