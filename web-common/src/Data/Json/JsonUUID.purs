module Data.Json.JsonUUID where

import Data.Generic.Rep (class Generic)
import Data.Generic.Rep.Show (genericShow)
import Data.Lens (Iso')
import Data.Lens.Iso.Newtype (_Newtype)
import Data.Maybe (Maybe(..))
import Data.Newtype (class Newtype)
import Data.UUID (UUID)
import Data.UUID as UUID
import Foreign (fail, ForeignError(TypeMismatch), readString)
import Foreign.Class (class Decode, class Encode, encode)
import Prelude

newtype JsonUUID
  = JsonUUID UUID

derive instance newtypeJsonUUID :: Newtype JsonUUID _

derive instance eqJsonUUID :: Eq JsonUUID

derive instance genericJsonUUID :: Generic JsonUUID _

derive instance ordJsonUUID :: Ord JsonUUID

instance showJsonUUID :: Show JsonUUID where
  show = genericShow

instance encodeJsonUUID :: Encode JsonUUID where
  encode (JsonUUID uuid) = encode $ UUID.toString uuid

instance decodeJsonUUID :: Decode JsonUUID where
  decode value =
    readString value
      >>= \x -> case UUID.parseUUID x of
          Nothing -> fail $ TypeMismatch "UUID" x
          Just uuid -> pure $ JsonUUID uuid

_JsonUUID :: Iso' JsonUUID UUID
_JsonUUID = _Newtype
