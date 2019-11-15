module Data.Json.JsonEither where

import Prelude
import Control.Alt ((<|>))
import Data.Either (Either(..))
import Data.Generic.Rep (class Generic)
import Data.Generic.Rep.Show (genericShow)
import Data.Lens (Iso')
import Data.Lens.Iso.Newtype (_Newtype)
import Data.Newtype (class Newtype)
import Foreign.Class (class Decode, class Encode, decode, encode)
import Foreign.Index (readProp)
import Foreign.Object as Object

newtype JsonEither a b
  = JsonEither (Either a b)

derive instance newtypeJsonEither :: Newtype (JsonEither a b) _

derive instance eqJsonEither :: (Eq a, Eq b) => Eq (JsonEither a b)

derive instance genericJsonEither :: Generic (JsonEither a b) _

instance showJsonEither :: (Show a, Show b) => Show (JsonEither a b) where
  show = genericShow

instance encodeJsonEither :: (Encode a, Encode b) => Encode (JsonEither a b) where
  encode (JsonEither (Left a)) = encode $ Object.singleton "Left" a
  encode (JsonEither (Right b)) = encode $ Object.singleton "Right" b

instance decodeJsonEither :: (Decode a, Decode b) => Decode (JsonEither a b) where
  decode value =
    JsonEither
      <$> ( (readProp "Left" value >>= (map Left <<< decode))
            <|> (readProp "Right" value >>= (map Right <<< decode))
        )

_JsonEither :: forall a b. Iso' (JsonEither a b) (Either a b)
_JsonEither = _Newtype
