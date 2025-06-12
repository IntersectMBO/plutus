-- Copyright 2024 Lennart Augustsson
-- See LICENSE file for full license.
module Control.Exception.Internal(
  throw,
  Exception(..),
  SomeException,
  ) where
import Data.Char_Type
import Data.Typeable

throw :: forall e a. Exception e => e -> a

data SomeException

class (Typeable e, Show e) => Exception e where
    toException      :: e -> SomeException
    fromException    :: SomeException -> Maybe e
    displayException :: e -> String
