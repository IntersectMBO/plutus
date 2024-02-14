{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE LambdaCase         #-}

module PlutusTx.Blueprint.Purpose where

import Prelude

import Data.Aeson (ToJSON (..))
import Data.Aeson qualified as Json
import Data.Text (Text)
import Data.Text qualified as Text

data Purpose = Spend | Mint | Withdraw | Publish
  deriving stock (Eq, Ord, Show)

instance ToJSON Purpose where
  toJSON = Json.String . purposeToText

purposeToText :: Purpose -> Text
purposeToText =
  Text.pack . \case
    Spend -> "spend"
    Mint -> "mint"
    Withdraw -> "withdraw"
    Publish -> "publish"
