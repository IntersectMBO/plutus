{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

module PlutusTx.Blueprint.Purpose where

import Prelude

import Data.Aeson (ToJSON (..))
import Data.Aeson qualified as Json
import Data.Text (Text)
import Language.Haskell.TH.Syntax (Lift)

{-|
  As per CIP-57, a validator arguments (redeemer, datum) and validator parameters
  all must specify a purpose that indicates in which context they are used. -}
data Purpose = Spend | Mint | Withdraw | Publish
  deriving stock (Eq, Ord, Show, Lift)

instance ToJSON Purpose where
  toJSON = Json.String . purposeToText

purposeToText :: Purpose -> Text
purposeToText = \case
  Spend -> "spend"
  Mint -> "mint"
  Withdraw -> "withdraw"
  Publish -> "publish"
