-- This module exposes a data type that is equal to the Data.Tuple type. But
-- only the minimium methods for encoding and decoding are provided, as their only
-- use case is to serve as a serialization mechanism with Haskell tuple type.
module Data.Json.JsonNTuple where

import Prelude
import Data.Array as Array
import Data.List (List(..))
import Data.List as List
import Data.Tuple (Tuple(..))
import Foreign (ForeignError(..), fail, readArray)
import Foreign.Class (class Decode, class Encode, decode, encode)

data JsonNTuple a b
  = JsonNTuple a b

infixr 6 JsonNTuple as /\

infixr 6 type JsonNTuple as /\

instance showTuple :: (Show a, Show b) => Show (JsonNTuple a b) where
  show (JsonNTuple a b) = show a <> " /\\ " <> show b

derive instance eqTuple :: (Eq a, Eq b) => Eq (JsonNTuple a b)

instance encodeJsonNTuple6 :: (Encode a, Encode b, Encode c, Encode d, Encode e, Encode f) => Encode (a /\ b /\ c /\ d /\ e /\ f) where
  encode (a /\ b /\ c /\ d /\ e /\ f) = encode $ [ encode a, encode b, encode c, encode d, encode e, encode f ]
else instance encodeJsonNTuple5 :: (Encode a, Encode b, Encode c, Encode d, Encode e) => Encode (a /\ b /\ c /\ d /\ e) where
  encode (a /\ b /\ c /\ d /\ e) = encode $ [ encode a, encode b, encode c, encode d, encode e ]
else instance encodeJsonNTuple4 :: (Encode a, Encode b, Encode c, Encode d) => Encode (a /\ b /\ c /\ d) where
  encode (a /\ b /\ c /\ d) = encode $ [ encode a, encode b, encode c, encode d ]
else instance encodeJsonNTuple3 :: (Encode a, Encode b, Encode c) => Encode (a /\ b /\ c) where
  encode (a /\ b /\ c) = encode $ [ encode a, encode b, encode c ]
else instance encodeJsonNTuple2 :: (Encode a, Encode b) => Encode (a /\ b) where
  encode (a /\ b) = encode [ encode a, encode b ]

instance decodeJsonNTuple2 :: (Decode a, Decode b) => Decode (a /\ b) where
  decode value = do
    elements <- List.fromFoldable <$> readArray value
    consume elements
    where
    consume Nil = fail $ ForeignError "Decoding a JsonTuple, expected to see an array with exactly 2 elements, got 0"

    consume (Cons x Nil) = fail $ ForeignError "Decoding a JsonTuple, expected to see an array with exactly 2 elements, got 1."

    consume (Cons x (Cons y Nil)) = do
      a <- decode x
      b <- decode y
      pure $ a /\ b

    consume (Cons x ys) = do
      a <- decode x
      b <- decode $ encode $ Array.fromFoldable ys
      pure $ a /\ b

fromTuple :: forall a b. Tuple a b -> JsonNTuple a b
fromTuple (Tuple a b) = JsonNTuple a b

toTuple :: forall a b. JsonNTuple a b -> Tuple a b
toTuple (JsonNTuple a b) = Tuple a b
