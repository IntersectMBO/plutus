module Validation where

import Prelude

import Data.Foldable (class Foldable)
import Data.Generic (class Generic)
import Data.List (List(..))
import Data.List as List

class Validation a where
  validate ::  a -> Array (WithPath ValidationError)

data ValidationError
  = Required
  | Unsupported

derive instance eqValidationError :: Eq ValidationError
derive instance genericValidationError :: Generic ValidationError

instance showValidationError :: Show ValidationError where
  show Required = "Required"
  show Unsupported = "Unsupported"

------------------------------------------------------------

newtype WithPath a = WithPath { path :: List String, value :: a }

derive instance eqWithPath :: Eq a => Eq (WithPath a)

derive instance functorWithPath :: Functor WithPath

instance showWithPath :: Show a => Show (WithPath a) where
  show (WithPath { path, value }) = List.intercalate "." path <> ": " <> show value

noPath :: forall a. a -> WithPath a
noPath value = WithPath { path: Nil, value }

withPath :: forall a f. Foldable f => f String -> a -> WithPath a
withPath path value = WithPath { path: List.fromFoldable path, value }

addPath :: forall a. String -> WithPath a -> WithPath a
addPath parent (WithPath {path, value}) = WithPath { path: Cons parent path, value }
