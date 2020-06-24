module Data.Json.JsonMap where

import Prelude
import Control.Alternative ((<|>))
import Data.Generic.Rep (class Generic)
import Data.Generic.Rep.Show (genericShow)
import Data.Lens (Iso')
import Data.Lens.Iso.Newtype (_Newtype)
import Data.Map (Map)
import Data.Map as Map
import Data.Newtype (class Newtype)
import Data.Profunctor.Strong (first)
import Data.Traversable (traverse)
import Data.Tuple (Tuple(..))
import Foreign (F, Foreign, ForeignError(..), fail, readArray, readNull)
import Foreign.Class (class Decode, class Encode, decode, encode)
import Foreign.Generic (encodeJSON)
import Foreign.Index (readProp)
import Foreign.Keys as Foreign
import Foreign.Object as Object

newtype JsonMap k v
  = JsonMap (Map k v)

derive instance newtypeJsonMap :: Newtype (JsonMap k v) _

derive instance eqJsonMap :: (Eq k, Eq v) => Eq (JsonMap k v)

derive instance genericJsonMap :: Generic (JsonMap k v) _

derive newtype instance semigroupJsonMap :: Ord k => Semigroup (JsonMap k v)

derive newtype instance monoidJsonMap :: Ord k => Monoid (JsonMap k v)

instance showJsonMap :: (Show k, Show v) => Show (JsonMap k v) where
  show = genericShow

instance encodeJsonMap :: (Encode k, Encode v) => Encode (JsonMap k v) where
  encode (JsonMap m) = encode $ Object.fromFoldable asPairs
    where
    asPairs :: Array (Tuple String v)
    asPairs = first encodeJSON <$> Map.toUnfoldable m

instance decodeJsonMap :: (Ord k, Decode k, Decode v) => Decode (JsonMap k v) where
  decode o = decodeAsObjectWithStringKeys o <|> decodeAsArrayOfPairs o <|> decodeAsNull o

decodeAsObjectWithStringKeys :: forall k v. Ord k => Decode k => Decode v => Foreign -> F (JsonMap k v)
decodeAsObjectWithStringKeys o = do
  keys <- Foreign.keys o
  asArray <-
    traverse
      ( \keyString -> do
          foreignValue <- readProp keyString o
          key <- decode $ encode keyString
          value <- decode foreignValue
          pure (Tuple key value)
      )
      keys
  pure $ JsonMap $ Map.fromFoldable asArray

decodeAsArrayOfPairs :: forall k v. Ord k => Decode k => Decode v => Foreign -> F (JsonMap k v)
decodeAsArrayOfPairs o = do
  pairs <- readArray o
  asArray <-
    traverse
      ( \foreignPair ->
          readArray foreignPair
            >>= case _ of
                [ foreignKey, foreignValue ] -> Tuple <$> decode foreignKey <*> decode foreignValue
                other -> fail $ TypeMismatch "Array (key-value pair)" "<Foreign>"
      )
      pairs
  pure $ JsonMap $ Map.fromFoldable asArray

decodeAsNull :: forall v k. Ord k => Foreign -> F (JsonMap k v)
decodeAsNull o = do
  _ <- readNull o
  pure mempty

_JsonMap :: forall k v. Iso' (JsonMap k v) (Map k v)
_JsonMap = _Newtype
