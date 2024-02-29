{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE LambdaCase         #-}

module PlutusTx.Blueprint.Purpose where

import Prelude

import Data.Aeson (ToJSON (..))
import Data.Aeson qualified as Json
import Data.Text (Text)
import Data.Text qualified as Text

{- | As per CIP-57, a validator arguments (redeemer, datum) and validator parameters
| all must specify a purpose that indicates in which context they are used.
-}
data Purpose = Spend | Mint | Withdraw | Publish
  deriving stock (Eq, Ord, Show)

instance ToJSON Purpose where
  toJSON = Json.String . purposeToText

purposeToText :: Purpose -> Text
purposeToText =
  Text.pack . \case
    Spend    -> "spend"
    Mint     -> "mint"
    Withdraw -> "withdraw"
    Publish  -> "publish"
