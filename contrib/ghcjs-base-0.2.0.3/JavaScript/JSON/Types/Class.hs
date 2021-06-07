{-# LANGUAGE DefaultSignatures, FlexibleContexts #-}

module JavaScript.JSON.Types.Class (
    -- * Type classes
    -- ** Core JSON classes
      FromJSON(..)
    , ToJSON(..)

    -- ** Generic JSON classes
    , GFromJSON(..)
    , GToJSON(..)
    , genericToJSON
    , genericParseJSON
    ) where

import JavaScript.JSON.Types.Internal

import GHC.Generics

class GToJSON f where gToJSON :: Options -> f a -> Value
class GFromJSON f where gParseJSON :: Options -> Value -> Parser (f a)

genericToJSON :: (Generic a, GToJSON (Rep a)) => Options -> a -> Value
genericToJSON opts = gToJSON opts . from

genericParseJSON :: (Generic a, GFromJSON (Rep a)) => Options -> Value -> Parser a
genericParseJSON opts = fmap to . gParseJSON opts

class ToJSON a where
    toJSON   :: a -> Value
    default toJSON :: (Generic a, GToJSON (Rep a)) => a -> Value
    toJSON = genericToJSON defaultOptions

class FromJSON a where
    parseJSON :: Value -> Parser a
    default parseJSON :: (Generic a, GFromJSON (Rep a)) => Value -> Parser a
    parseJSON = genericParseJSON defaultOptions
