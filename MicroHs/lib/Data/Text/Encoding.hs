module Data.Text.Encoding (
    -- XXX: add more
    decodeLatin1,
    decodeASCIIPrefix,

    decodeASCII,
    decodeUtf8,
    decodeUtf16LE,
    decodeUtf16BE,
    decodeUtf32LE,
    decodeUtf32BE,

    encodeUtf8,
    encodeUtf16LE,
    encodeUtf16BE,
    encodeUtf32LE,
    encodeUtf32BE,
) where

import Data.Bits
import Data.ByteString (ByteString, isValidUtf8)
import Data.ByteString qualified as BS
import Data.Char
import Data.Text
import Data.Word (Word8)
import Unsafe.Coerce (unsafeCoerce)

intToWord8 :: Int -> Word8
intToWord8 i = unsafeCoerce (i .&. 0xFF) -- Safety: Int and Word8 have the same representation and `i .&. 0xFF` ensures that the value is in the Word8 range

word8ToInt :: Word8 -> Int
word8ToInt w = unsafeCoerce w -- Safety: Int and Word8 have the same representation and a Word8 is in the Int range

isValidASCII :: ByteString -> Bool
isValidASCII = BS.all (< 0x80)

decodeLatin1 :: ByteString -> Text
decodeLatin1 = pack . unsafeCoerce BS.unpack -- Safety: Char and Word8 have the same representation & a Latin-1 byte is the correct Unicode code point

decodeASCIIPrefix :: ByteString -> (Text, ByteString)
decodeASCIIPrefix bs = let (a, b) = BS.span (< 0x80) bs in (unsafeCoerce a, b) -- Safety: the ByteString is valid ASCII, which is also valid UTF-8 and Text uses UTF-8 encoding

decodeASCII :: ByteString -> Text
decodeASCII bs
    | isValidASCII bs = unsafeCoerce bs -- Safety: the ByteString is valid ASCII, which is also valid UTF-8 and Text uses UTF-8 encoding
    | otherwise = error "Data.Text.Encoding.decodeASCII: invalid"

decodeUtf8 :: ByteString -> Text
decodeUtf8 bs
    | isValidUtf8 bs = unsafeCoerce bs -- Safety: the ByteString is valid UTF-8 and Text uses UTF-8 encoding
    | otherwise = error "Data.Text.Encoding.decodeUtf8: invalid"

decodeUtf16LE :: ByteString -> Text
decodeUtf16LE bs
    | BS.length bs .&. 0x1 /= 0 = error "Data.Text.Encoding.decodeUtf16LE: invalid size"
    | otherwise = pack (decode $ BS.unpack bs)
  where
    decode [] = []
    decode (x1 : x2 : xs) | x2 <= 0xD7 || x2 >= 0xE0 = chr (word8ToInt x1 .|. (word8ToInt x2 `shiftL` 8)) : decode xs
    decode (x1 : x2 : x3 : x4 : xs) | x2 .&. 0xFC == 0xD8 && x4 .&. 0xFC == 0xDC =
      let w1 = word8ToInt x1 .|. (word8ToInt x2 `shiftL` 8)
          w2 = word8ToInt x3 .|. (word8ToInt x4 `shiftL` 8)
      in chr (((w2 .&. 0x3FF) .|. ((w1 .&. 0x3FF) `shiftL` 10)) + 0x10000) : decode xs
    decode _ = error "Data.Text.Encoding.decodeUtf16LE: invalid"

decodeUtf16BE :: ByteString -> Text
decodeUtf16BE bs
    | BS.length bs .&. 0x1 /= 0 = error "Data.Text.Encoding.decodeUtf16BE: invalid size"
    | otherwise = pack (decode $ BS.unpack bs)
  where
    decode [] = []
    decode (x1 : x2 : xs) | x1 <= 0xD7 || x1 >= 0xE0 = chr ((word8ToInt x1 `shiftL` 8) .|. word8ToInt x2) : decode xs
    decode (x1 : x2 : x3 : x4 : xs) | x1 .&. 0xFC == 0xD8 && x3 .&. 0xFC == 0xDC =
      let w1 = (word8ToInt x1 `shiftL` 8) .|. word8ToInt x2
          w2 = (word8ToInt x3 `shiftL` 8) .|. word8ToInt x4
      in chr (((w2 .&. 0x3FF) .|. ((w1 .&. 0x3FF) `shiftL` 10)) + 0x10000) : decode xs
    decode _ = error "Data.Text.Encoding.decodeUtf16BE: invalid"

decodeUtf32LE :: ByteString -> Text
decodeUtf32LE bs
    | BS.length bs .&. 0x3 /= 0 = error "Data.Text.Encoding.decodeUtf32LE: invalid size"
    | otherwise = pack (decode $ BS.unpack bs)
  where
    decode [] = []
    decode (x1 : x2 : x3 : x4 : xs) | x2 <= 0xD7 || x2 >= 0xE0 = chr (word8ToInt x1 .|. (word8ToInt x2 `shiftL` 8) .|. (word8ToInt x3 `shiftL` 16) .|. (word8ToInt x4 `shiftL` 24)) : decode xs
    decode _ = error "Data.Text.Encoding.decodeUtf32LE: impossible" -- length is not a multiple of 4

decodeUtf32BE :: ByteString -> Text
decodeUtf32BE bs
    | BS.length bs .&. 0x3 /= 0 = error "Data.Text.Encoding.decodeUtf32BE: invalid size"
    | otherwise = pack (decode $ BS.unpack bs)
  where
    decode [] = []
    decode (x1 : x2 : x3 : x4 : xs) | x3 <= 0xD7 || x3 >= 0xE0 = chr ((word8ToInt x1 `shiftL` 24) .|. (word8ToInt x2 `shiftL` 16) .|. (word8ToInt x3 `shiftL` 8) .|. word8ToInt x4) : decode xs
    decode _ = error "Data.Text.Encoding.decodeUtf32BE: impossible" -- length is not a multiple of 4

encodeUtf8 :: Text -> ByteString
encodeUtf8 = unsafeCoerce -- Safety: Text uses UTF-8 encoding

encodeUtf16LE :: Text -> ByteString
encodeUtf16LE = BS.pack . concatMap f . unpack
  where
    f c =
        let w = ord c
        in if c <= '\xFFFF'
            then [intToWord8 w, intToWord8 (w `shiftR` 8)]
            else
                let u = w - 0x10000
                    w1 = 0xD800 + u `shiftR` 10
                    w2 = 0xDC00 + u .&. 0x3FF
                in [intToWord8 w1, intToWord8 (w1 `shiftR` 8), intToWord8 w2, intToWord8 (w2 `shiftR` 8)]

encodeUtf16BE :: Text -> ByteString
encodeUtf16BE = BS.pack . concatMap f . unpack
  where
    f c =
        let w = ord c
        in if c <= '\xFFFF'
            then [intToWord8 (w `shiftR` 8), intToWord8 w]
            else
                let u = w - 0x10000
                    w1 = 0xD800 + u `shiftR` 10
                    w2 = 0xDC00 + u .&. 0x3FF
                in [intToWord8 (w1 `shiftR` 8), intToWord8 w1, intToWord8 (w2 `shiftR` 8), intToWord8 w2]

encodeUtf32LE :: Text -> ByteString
encodeUtf32LE = BS.pack . concatMap f . unpack
  where
    f c =
        let w = ord c
        in
            [ intToWord8 w
            , intToWord8 (w `shiftR` 8)
            , intToWord8 (w `shiftR` 16)
            , intToWord8 (w `shiftR` 24)
            ]

encodeUtf32BE :: Text -> ByteString
encodeUtf32BE = BS.pack . concatMap f . unpack
  where
    f c =
        let w = ord c
        in
            [ intToWord8 (w `shiftR` 24)
            , intToWord8 (w `shiftR` 16)
            , intToWord8 (w `shiftR` 8)
            , intToWord8 w
            ]
