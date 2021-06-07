{-# LANGUAGE DeriveDataTypeable, DefaultSignatures, FlexibleContexts #-}

module JavaScript.JSON.Types ( Value
                             , Object
                             , Options(..)
                             , defaultOptions
                             , SumEncoding(..)
                             , defaultTaggedObject
                             , camelTo
                             ) where

import Control.Applicative
import Control.DeepSeq

import Data.Aeson.Types (Options(..), SumEncoding(..))

import Data.Maybe
import Data.Typeable
import Data.JSString

import GHC.Generics

import           JavaScript.JSON.Types.Class
import           JavaScript.JSON.Types.Internal
import qualified JavaScript.JSON.Types.Internal as I

runParser = undefined

-- | Run a 'Parser'.
parse :: (a -> Parser b) -> a -> Result b
parse m v = runParser (m v) Error Success
{-# INLINE parse #-}

-- | Run a 'Parser' with a 'Maybe' result type.
parseMaybe :: (a -> Parser b) -> a -> Maybe b
parseMaybe m v = runParser (m v) (const Nothing) Just
{-# INLINE parseMaybe #-}

-- | Run a 'Parser' with an 'Either' result type.
parseEither :: (a -> Parser b) -> a -> Either String b
parseEither m v = runParser (m v) Left Right
{-# INLINE parseEither #-}

-- | If the inner @Parser@ failed, modify the failure message using the
-- provided function. This allows you to create more descriptive error messages.
-- For example:
--
-- > parseJSON (Object o) = modifyFailure
-- >     ("Parsing of the Foo value failed: " ++)
-- >     (Foo <$> o .: "someField")
--
-- Since 0.6.2.0
modifyFailure :: (JSString -> JSString) -> Parser a -> Parser a
modifyFailure = undefined -- f (Parser p) = Parser $ \kf -> p (kf . f)

-- | Construct a 'Pair' from a key and a value.
(.=) :: ToJSON a => JSString -> a -> Pair
name .= value = (name, toJSON value)
{-# INLINE (.=) #-}

-- | Convert a value from JSON, failing if the types do not match.
fromJSON :: (FromJSON a) => Value -> Result a
fromJSON = I.parse parseJSON
{-# INLINE fromJSON #-}

(.:) :: FromJSON a => Object -> JSString -> Parser a
obj .: key = case I.lookup key obj of
               Nothing -> fail $ "key " ++ show key ++ " not present"
               Just v  -> parseJSON v
{-# INLINE (.:) #-}

(.:?) :: FromJSON a => Object -> JSString -> Parser (Maybe a)
obj .:? key = case I.lookup key obj of
                Nothing -> pure Nothing
                Just v  -> Just <$> parseJSON v
{-# INLINE (.:?) #-}

(.!=) :: Parser (Maybe a) -> a -> Parser a
pmval .!= val = fromMaybe val <$> pmval
{-# INLINE (.!=) #-}
