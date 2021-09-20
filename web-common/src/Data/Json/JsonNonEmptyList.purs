module Data.Json.JsonNonEmptyList where

import Prelude
import Data.Array as Array
import Data.Foldable (class Foldable, foldMap, foldlDefault, foldrDefault)
import Data.Generic.Rep (class Generic)
import Data.Generic.Rep.Show (genericShow)
import Data.List.NonEmpty (NonEmptyList)
import Data.List.NonEmpty as NEL
import Data.Maybe (Maybe(..))
import Data.Newtype (class Newtype)
import Foreign (F, ForeignError(..), fail)
import Foreign.Class (class Decode, class Encode, decode, encode)

newtype JsonNonEmptyList a
  = JsonNonEmptyList (NonEmptyList a)

derive instance genericJsonNonEmptyList :: Generic (JsonNonEmptyList a) _

derive instance newtypeJsonNonEmptyList :: Newtype (JsonNonEmptyList a) _

derive instance eqJsonNonEmptyList :: Eq a => Eq (JsonNonEmptyList a)

instance showJsonNonEmptyList :: Show a => Show (JsonNonEmptyList a) where
  show = genericShow

instance encodeJsonNonEmptyList :: Encode a => Encode (JsonNonEmptyList a) where
  encode (JsonNonEmptyList x) = encode $ Array.fromFoldable x

instance decodeJsonNonEmptyList :: Decode a => Decode (JsonNonEmptyList a) where
  decode value = do
    xs <- (decode value :: F (Array a))
    case NEL.fromFoldable xs of
      Nothing -> fail $ ForeignError "Decoding a JsonNonEmptyList, found an empty Array."
      Just nel -> pure $ JsonNonEmptyList nel

instance foldableJsonNonEmptyList :: Foldable JsonNonEmptyList where
  foldMap f (JsonNonEmptyList x) = foldMap f x
  foldl f x = foldlDefault f x
  foldr f x = foldrDefault f x
