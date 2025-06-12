-- Copyright 2023 Lennart Augustsson
-- See LICENSE file for full license.
module Data.Text(
  Text,
  pack, unpack,
  empty,
  append,
  null,
  head,
  tail,
  uncons,
  ) where
import Data.Monoid
import Prelude hiding (head, null, tail)
import Prelude qualified
--import Data.String
import Data.Semigroup

newtype Text = T String

instance Eq Text where
  (==) = cmp (==)
  (/=) = cmp (/=)

instance Ord Text where
  (<)  = cmp (<)
  (<=) = cmp (<=)
  (>)  = cmp (>)
  (>=) = cmp (>=)

cmp :: (String -> String -> Bool) -> (Text -> Text -> Bool)
cmp op (T x) (T y) = op x y

instance Show Text where
  showsPrec p = showsPrec p . unpack

--instance IsString Text where
--  fromString = pack

instance Semigroup Text where
  (<>) = append

instance Monoid Text where
  mempty = empty

empty :: Text
empty = T ""

pack :: String -> Text
pack = T

unpack :: Text -> String
unpack (T t) = t

append :: Text -> Text -> Text
append (T x) (T y) = T (x ++ y)

null :: Text -> Bool
null (T bs) = Prelude.null bs

head :: Text -> Char
head (T t) = Prelude.head t

tail :: Text -> Text
tail (T t) = T (Prelude.tail t)

uncons :: Text -> Maybe (Char, Text)
uncons t | null t    = Nothing
         | otherwise = Just (head t, tail t)

{-
import qualified Data.ByteString.Char8 as BS

newtype Text = T BS.ByteString

instance Eq Text where
  (==) = cmp (==)
  (/=) = cmp (/=)

instance Ord Text where
  (<)  = cmp (<)
  (<=) = cmp (<=)
  (>)  = cmp (>)
  (>=) = cmp (>=)

cmp :: (BS.ByteString -> BS.ByteString -> Bool) -> (Text -> Text -> Bool)
cmp op (T x) (T y) = op x y

instance Show Text where
  showsPrec p = showsPrec p . unpack

--instance IsString Text where
--  fromString = pack

instance Semigroup Text where
  (<>) = append

instance Monoid Text where
  mempty = empty

empty :: Text
empty = pack []

pack :: String -> Text
pack = T . BS.pack

unpack :: Text -> String
unpack (T t) = BS.unpack t

append :: Text -> Text -> Text
append (T x) (T y) = T (BS.append x y)

null :: Text -> Bool
null (T bs) = BS.null bs

head :: Text -> Char
head (T t) = BS.head t

tail :: Text -> Text
tail (T t) = T (BS.tail t)

uncons :: Text -> Maybe (Char, Text)
uncons t | null t    = Nothing
         | otherwise = Just (head t, tail t)
-}
