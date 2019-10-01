module Data.Json.JsonTuple where

import Prelude
import Data.Generic.Rep (class Generic)
import Data.Generic.Rep.Show (genericShow)
import Data.Lens (Iso')
import Data.Lens.Iso.Newtype (_Newtype)
import Data.Newtype (class Newtype)
import Data.Tuple (Tuple(..))
import Foreign (ForeignError(..), fail, readArray)
import Foreign.Class (class Decode, class Encode, decode, encode)

newtype JsonTuple a b
  = JsonTuple (Tuple a b)

derive instance newtypeJsonTuple :: Newtype (JsonTuple a b) _

derive instance eqJsonTuple :: (Eq a, Eq b) => Eq (JsonTuple a b)

derive instance ordJsonTuple :: (Ord a, Ord b) => Ord (JsonTuple a b)

derive instance genericJsonTuple :: Generic (JsonTuple a b) _

derive instance functorJsonTuple :: Functor (JsonTuple a)

instance showJsonTuple :: (Show a, Show b) => Show (JsonTuple a b) where
  show = genericShow

instance encodeJsonTuple :: (Encode a, Encode b) => Encode (JsonTuple a b) where
  encode (JsonTuple (Tuple a b)) = encode [ encode a, encode b ]

instance decodeJsonTuple :: (Decode a, Decode b) => Decode (JsonTuple a b) where
  decode value = do
    xs <- readArray value
    case xs of
      [ x, y ] -> do
        a <- decode x
        b <- decode y
        pure $ JsonTuple (Tuple a b)
      _ -> fail $ ForeignError "Decoding a JsonTuple, expected to see an array with exactly 2 elements."

_JsonTuple :: forall k v. Iso' (JsonTuple k v) (Tuple k v)
_JsonTuple = _Newtype
