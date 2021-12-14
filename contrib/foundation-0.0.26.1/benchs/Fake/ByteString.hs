module Fake.ByteString
    ( ByteString
    , pack
    , length
    , splitAt
    , take
    , takeWhile
    , break
    , reverse
    , filter
    , foldl'
    , foldl1'
    , foldr
    , and
    , all
    , any
    , readInt
    , readInteger
    , unpack
    , concat
    ) where

import Prelude (undefined, Maybe(..))
import Data.Word

data ByteString = ByteString

pack _      = ByteString
length      = undefined
splitAt _ _ = (undefined, undefined)
take        = undefined
break   _ _ = (undefined, undefined)
takeWhile _ _ = undefined
reverse     = undefined
filter _    = undefined
foldl' :: (Word8 -> a -> a) -> a -> ByteString -> a
foldl' _ _ _ = undefined
foldl1' :: (Word8 -> Word8 -> Word8) -> ByteString -> a
foldl1' _ _ = undefined
foldr :: (a -> Word8 -> a) -> a -> ByteString -> a
foldr _ _ _ = undefined
and _ _ = undefined
all _ _ = undefined
any _ _ = undefined
concat :: [ByteString] -> ByteString
concat _ = undefined
unpack :: ByteString -> [Word8]
unpack = undefined

readInt :: ByteString -> Maybe (a,b)
readInt _    = undefined
readInteger :: ByteString -> Maybe (a,b)
readInteger _ = undefined
