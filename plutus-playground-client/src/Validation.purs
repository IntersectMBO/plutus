module Validation where

import Prelude

import Data.Array as Array
import Data.Foldable (class Foldable)
import Data.Generic.Rep (class Generic)

class Validation a where
  validate ::  a -> Array (WithPath ValidationError)

data ValidationError
  = Required
  | Unsupported

derive instance eqValidationError :: Eq ValidationError
derive instance genericValidationError :: Generic ValidationError _

instance showValidationError :: Show ValidationError where
  show Required = "Required"
  show Unsupported = "Unsupported"

------------------------------------------------------------

newtype WithPath a = WithPath { path :: Array String, value :: a }

derive instance eqWithPath :: Eq a => Eq (WithPath a)

derive instance functorWithPath :: Functor WithPath

instance showWithPath :: Show a => Show (WithPath a) where
  show (WithPath { path, value }) = Array.intercalate "." path <> ": " <> show value

showPathValue :: forall a. Show a => WithPath a -> String
showPathValue (WithPath {value}) = show value

noPath :: forall a. a -> WithPath a
noPath value = WithPath { path: [], value }

withPath :: forall a f. Foldable f => f String -> a -> WithPath a
withPath path value = WithPath { path: Array.fromFoldable path, value }

addPath :: forall a. String -> WithPath a -> WithPath a
addPath parent (WithPath {path, value}) = WithPath { path: Array.cons parent path, value }

joinPath :: forall a. Array String -> WithPath a -> WithPath a
joinPath ancestors (WithPath {path, value}) = WithPath { path: ancestors <> path, value }
