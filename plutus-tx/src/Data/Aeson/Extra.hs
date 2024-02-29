module Data.Aeson.Extra (
  optionalField,
  requiredField,
) where

import Prelude

import Data.Aeson (ToJSON (..))
import Data.Aeson qualified as Aeson
import Data.Aeson.KeyMap qualified as KeyMap

optionalField :: (ToJSON a) => Aeson.Key -> Maybe a -> Aeson.Object -> Aeson.Object
optionalField = maybe id . requiredField

requiredField :: (ToJSON a) => Aeson.Key -> a -> Aeson.Object -> Aeson.Object
requiredField key value = KeyMap.insert key (toJSON value)
