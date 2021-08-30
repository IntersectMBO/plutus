module Data.Json.JsonTriple where

import Prelude
import Data.Array as Array
import Data.Generic.Rep (class Generic)
import Data.List (List(..))
import Data.List as List
import Data.Tuple.Nested (type (/\), (/\))
import Foreign (ForeignError(..), fail, readArray)
import Foreign.Class (class Decode, class Encode, decode, encode)

newtype JsonTriple a b c
  = JsonTriple (a /\ b /\ c)

derive instance genericJsonTriple :: Generic (JsonTriple a b c) _

instance encodeJsonTriple :: (Encode a, Encode b, Encode c) => Encode (JsonTriple a b c) where
  encode (JsonTriple (a /\ b /\ c)) = encode [ encode a, encode b, encode c ]

instance decodeJsonTriple :: (Decode a, Decode b, Decode c) => Decode (JsonTriple a b c) where
  decode value = do
    elements <- List.fromFoldable <$> readArray value
    consume elements
    where
    consume Nil = fail $ ForeignError "Decoding a JsonTriple, expected to see an array with exactly 3 elements, got 0"

    consume (Cons x Nil) = fail $ ForeignError "Decoding a JsonTriple, expected to see an array with exactly 3 elements, got 1."

    consume (Cons x (Cons y Nil)) = fail $ ForeignError "Decoding a JsonTriple, expected to see an array with exactly 3 elements, got 2."

    consume (Cons x (Cons y (Cons z Nil))) = do
      a <- decode x
      b <- decode y
      c <- decode z
      pure $ JsonTriple (a /\ b /\ c)

    consume (Cons x (Cons y zs)) = do
      a <- decode x
      b <- decode y
      c <- decode $ encode $ Array.fromFoldable zs
      pure $ JsonTriple (a /\ b /\ c)
