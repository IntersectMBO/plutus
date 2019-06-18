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

instance encodeRawJson :: Encode RawJson where
  encode (RawJson string) = unsafeToForeign string

instance decodeRawJson :: Decode RawJson where
  decode value = RawJson <$> readString value

------------------------------------------------------------
newtype JsonTuple a b
  = JsonTuple (Tuple a b)

derive instance newtypeJsonTuple :: Newtype (JsonTuple a b) _

derive instance eqJsonTuple :: (Eq a, Eq b) => Eq (JsonTuple a b)

derive instance genericJsonTuple :: Generic (JsonTuple a b) _

derive instance functorJsonTuple :: Functor (JsonTuple a)

instance showJsonTuple :: (Show a, Show b) => Show (JsonTuple a b) where
  show = genericShow

instance encodeJsonTuple :: (Encode a, Encode b) => Encode (JsonTuple a b) where
  encode (JsonTuple (Tuple a b)) = encode [encode a, encode b]

instance decodeJsonTuple :: (Decode a, Decode b) => Decode (JsonTuple a b) where
  decode value = do
    xs <- readArray value
    case xs of
      [x, y] -> do
        a <- decode x
        b <- decode y
        pure $ JsonTuple (Tuple a b)
      _ -> fail $ ForeignError "Decoding a JsonTuple, expected to see an array with exactly 2 elements."

------------------------------------------------------------
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

------------------------------------------------------------
newtype JsonNonEmptyList a
  = JsonNonEmptyList (NonEmptyList a)

derive instance genericJsonNonEmptyList :: Generic (JsonNonEmptyList a) _

derive instance newtypeJsonNonEmptyList :: Newtype (JsonNonEmptyList a) _

derive instance eqJsonNonEmptyList :: Eq a => Eq (JsonNonEmptyList a)

instance showJsonNonEmptyList :: Show a => Show (JsonNonEmptyList a) where
  show = genericShow

instance encodeJsonNonEmptyList :: Encode a => Encode (JsonNonEmptyList a) where
  encode (JsonNonEmptyList x) = b
    where
    a = Array.fromFoldable x

    b = encode a

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
