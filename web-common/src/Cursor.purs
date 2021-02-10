-- | A cursor is an Array with a pointer to the 'current' item, plus
-- some guarantees* that you cannot get into an invalid state.
--
-- * Mostly guaranteed by using smart constructors and judicious exports.
module Cursor
  ( Cursor
  , current
  , first
  , last
  , empty
  , singleton
  , snoc
  , deleteAt
  , fromArray
  , toArray
  , mapWithIndex
  , null
  , length
  , _current
  , setIndex
  , getIndex
  , left
  , right
  ) where

import Control.Monad.Gen.Class (chooseInt)
import Data.Array as Array
import Data.Foldable (class Foldable, foldMap, foldl, foldr)
import Data.Generic.Rep (class Generic)
import Data.Lens (Traversal', wander)
import Data.Lens.Index (class Index)
import Data.Maybe (Maybe, fromMaybe, maybe)
import Data.Ord as Ord
import Data.Traversable (class Traversable, sequenceDefault, traverse)
import Foreign (ForeignError(..), fail, readArray, readInt)
import Foreign.Class (class Decode, class Encode, decode, encode)
import Prelude (class Eq, class Functor, class Ord, class Show, bind, map, otherwise, pure, show, (#), ($), (+), (-), (<$>), (<<<), (<>), (>=), (>>>))
import Test.QuickCheck.Arbitrary (class Arbitrary, arbitrary)
import Test.QuickCheck.Gen (arrayOf)

data Cursor a
  = Cursor Int (Array a)

derive instance eqCursor :: Eq a => Eq (Cursor a)

derive instance ordCursor :: Ord a => Ord (Cursor a)

derive instance functorCursor :: Functor Cursor

derive instance genericCursor :: Generic (Cursor a) _

instance foldableCursor :: Foldable Cursor where
  foldr f acc (Cursor _ xs) = foldr f acc xs
  foldl f acc (Cursor _ xs) = foldl f acc xs
  foldMap f (Cursor _ xs) = foldMap f xs

instance traversableCursor :: Traversable Cursor where
  traverse f (Cursor n xs) = Cursor n <$> traverse f xs
  sequence = sequenceDefault

instance showCursor :: Show a => Show (Cursor a) where
  show (Cursor index xs) = "Cursor " <> show index <> " " <> show xs

instance arbitraryCursor :: Arbitrary a => Arbitrary (Cursor a) where
  arbitrary = do
    xs <- arrayOf arbitrary
    index <- chooseInt 0 (Array.length xs - 1)
    pure $ Cursor index xs

instance indexCursor :: Index (Cursor a) Int a where
  ix n =
    wander \coalg (Cursor index xs) ->
      Array.index xs n
        # maybe
            (pure xs)
            ( let
                f x = fromMaybe xs $ Array.updateAt n x xs
              in
                coalg >>> map f
            )
        # map (Cursor index)

instance encodeCursor :: Encode a => Encode (Cursor a) where
  encode (Cursor n xs) = encode [ encode n, encode xs ]

instance decodeCursor :: Decode a => Decode (Cursor a) where
  decode value = do
    xs <- readArray value
    case xs of
      [ x, y ] -> do
        index <- readInt x
        elements <- decode y
        pure $ Cursor index elements
      _ -> fail $ ForeignError "Decoding a Cursor, expected to see an array with exactly 2 elements."

_current :: forall a. Traversal' (Cursor a) a
_current =
  wander \coalg (Cursor index xs) ->
    Array.index xs index
      # maybe
          (pure xs)
          ( let
              f x = fromMaybe xs $ Array.updateAt index x xs
            in
              coalg >>> map f
          )
      # map (Cursor index)

clamp :: forall a. Cursor a -> Cursor a
clamp (Cursor index xs) =
  Cursor
    (Ord.clamp 0 (Array.length xs - 1) index)
    xs

empty :: forall a. Cursor a
empty = fromArray []

singleton :: forall a. a -> Cursor a
singleton = fromArray <<< Array.singleton

snoc :: forall a. Cursor a -> a -> Cursor a
snoc (Cursor index xs) x = last $ Cursor index (Array.snoc xs x)

deleteAt :: forall a. Int -> Cursor a -> Cursor a
deleteAt n cursor@(Cursor index xs) =
  fromMaybe cursor do
    let
      newIndex
        | n >= index = index
        | otherwise = index - 1
    newXs <- Array.deleteAt n xs
    pure $ clamp $ Cursor newIndex newXs

fromArray :: forall a. Array a -> Cursor a
fromArray xs = Cursor 0 xs

toArray :: forall a. Cursor a -> Array a
toArray (Cursor _ xs) = xs

mapWithIndex :: forall b a. (Int -> a -> b) -> Cursor a -> Cursor b
mapWithIndex f (Cursor index xs) = Cursor index (Array.mapWithIndex f xs)

null :: forall a. Cursor a -> Boolean
null (Cursor _ xs) = Array.null xs

length :: forall a. Cursor a -> Int
length (Cursor _ xs) = Array.length xs

current :: forall a. Cursor a -> Maybe a
current (Cursor index xs) = Array.index xs index

getIndex :: forall a. Cursor a -> Int
getIndex (Cursor index xs) = index

setIndex :: forall a. Int -> Cursor a -> Cursor a
setIndex newIndex (Cursor _ xs) = clamp $ Cursor newIndex xs

left :: forall a. Cursor a -> Cursor a
left (Cursor index xs) = clamp $ Cursor (index - 1) xs

right :: forall a. Cursor a -> Cursor a
right (Cursor index xs) = clamp $ Cursor (index + 1) xs

first :: forall a. Cursor a -> Cursor a
first (Cursor _ xs) = Cursor 0 xs

last :: forall a. Cursor a -> Cursor a
last (Cursor _ xs) = Cursor (Array.length xs - 1) xs
