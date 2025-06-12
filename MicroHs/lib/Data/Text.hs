module Data.Text(
  Text,
  pack, unpack,
  empty,
  singleton,
  append,
  null,
  length,
  head,
  tail,
  cons,
  snoc,
  uncons,
  replicate,
  splitOn,
  dropWhileEnd,
  words,
  foldr,
  concat,
  ) where
import Control.DeepSeq.Class
import Data.ByteString.Internal qualified as BS
import Data.List qualified as L
import Data.Monoid.Internal
import Data.String
import MiniPrelude hiding (head, length, null, tail, words)
import Prelude qualified ()
import Unsafe.Coerce (unsafeCoerce)

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

instance IsString Text where
  fromString = pack

instance Semigroup Text where
  (<>) = append

instance Monoid Text where
  mempty = empty

instance NFData Text where
  rnf (T bs) = seq bs ()

empty :: Text
empty = pack []

singleton :: Char -> Text
singleton c = pack [c]

pack :: String -> Text
pack s = T (_primitive "toUTF8" s)

unpack :: Text -> String
unpack (T t) = _primitive "fromUTF8" t

append :: Text -> Text -> Text
append (T x) (T y) = T (BS.append x y)

null :: Text -> Bool
null (T bs) = BS.null bs

length :: Text -> Int
length = L.length . unpack

head :: Text -> Char
head (T t)
  | BS.null t = error "Data.Text.head: empty"
  | otherwise = _primitive "headUTF8" t

cons :: Char -> Text -> Text
cons c t = singleton c `append` t

snoc :: Text -> Char -> Text
snoc t c = t `append` singleton c

tail :: Text -> Text
tail (T t)
  | BS.null t = error "Data.Text.tail: empty"
  | otherwise = _primitive "tailUTF8" t

uncons :: Text -> Maybe (Char, Text)
uncons t | null t    = Nothing
         | otherwise = Just (head t, tail t)

replicate :: Int -> Text -> Text
replicate = stimes

splitOn :: Text -> Text -> [Text]
splitOn s t = map pack $ splitOnList (unpack s) (unpack t)

dropWhileEnd :: (Char -> Bool) -> Text -> Text
dropWhileEnd p = pack . L.dropWhileEnd p . unpack

splitOnList :: Eq a => [a] -> [a] -> [[a]]
splitOnList [] = error "splitOn: empty"
splitOnList sep = loop []
  where
    loop r  [] = [reverse r]
    loop r  s@(c:cs) | Just t <- L.stripPrefix sep s = reverse r : loop [] t
                     | otherwise = loop (c:r) cs

words :: Text -> [Text]
words = map pack . L.words . unpack

foldr :: (Char -> a -> a) -> a -> Text -> a
foldr f z = L.foldr f z . unpack

concat :: [Text] -> Text
concat = L.foldr append empty
