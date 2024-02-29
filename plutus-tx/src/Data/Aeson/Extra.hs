{-# LANGUAGE LambdaCase #-}

module Data.Aeson.Extra (
  optionalField,
  requiredField,
  stripPrefix,
) where

import Prelude

import Data.Aeson (ToJSON (..))
import Data.Aeson qualified as Aeson
import Data.Aeson.KeyMap qualified as KeyMap
import Data.Char qualified as Char

optionalField :: (ToJSON a) => Aeson.Key -> Maybe a -> Aeson.Object -> Aeson.Object
optionalField = maybe id . requiredField

requiredField :: (ToJSON a) => Aeson.Key -> a -> Aeson.Object -> Aeson.Object
requiredField key value = KeyMap.insert key (toJSON value)

{- | A field label modifier that strips a prefix from the camelCased field name;
>>> stripPrefix "preamble" "preambleTitle"
"title"
-}
stripPrefix ::
  -- | Field prefix to strip
  String ->
  -- | Field name
  String ->
  String
stripPrefix prefix field = go (prefix, field)
 where
  go = \case
    (p1 : ps, f1 : fs) | p1 == f1 -> go (ps, fs)
    ([], f1 : fs) -> Char.toLower f1 : fs
    _ ->
      error
        $ "Unexpected field name '"
        ++ field
        ++ "', must start from '"
        ++ prefix
        ++ "' and have other characters after."
