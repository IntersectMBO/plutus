module Data.RawJson where

import Prelude

import Control.Alt ((<|>))
import Data.Array as Array
import Data.Either (Either(..))
import Data.Foldable (class Foldable, foldMap, foldlDefault, foldrDefault)
import Data.Generic.Rep (class Generic)
import Data.Generic.Rep.Show (genericShow)
import Data.Lens (Iso')
import Data.Lens.Iso.Newtype (_Newtype)
import Data.List.NonEmpty (NonEmptyList)
import Data.List.NonEmpty as NEL
import Data.Maybe (Maybe(..))
import Data.Newtype (class Newtype)
import Data.Tuple (Tuple(..))
import Foreign (ForeignError(..), F, fail, readArray, readString, unsafeToForeign)
import Foreign.Class (class Decode, class Encode, decode, encode)
import Foreign.Index (readProp)
import Foreign.Object as Object

newtype RawJson
  = RawJson String

derive instance genericRawJson :: Generic RawJson _

derive instance newtypeRawJson :: Newtype RawJson _

_RawJson :: Iso' RawJson String
_RawJson = _Newtype

instance showRawJson :: Show RawJson where show = genericShow

instance encodeRawJson :: Encode RawJson where
  encode (RawJson string) = unsafeToForeign string

instance decodeRawJson :: Decode RawJson where
  decode value = RawJson <$> readString value
