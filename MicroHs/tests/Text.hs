module Text where
import Data.Text as T
import Data.Text.Encoding

bs1 :: Text
bs1 = pack "abc"

bs2 :: Text
bs2 = pack "abd"

bs3 :: Text
bs3 = pack "ab"

bs4 :: Text
bs4 = pack "acd"

main :: IO ()
main = do
  print (unpack bs1)
  print bs1
  print $ bs1 `append` bs2
  print [ op x y | op <- [(==), (/=), (<), (<=), (>), (>=)]
                 , x <- [bs1, bs2, bs3, bs4]
                 , y <- [bs1, bs2, bs3, bs4]
        ]
  print [ compare x y | x <- [bs1, bs2, bs3, bs4], y <- [bs1, bs2, bs3, bs4] ]
  print ("abc" :: Text)
  print (T.head bs1)
  print (T.tail bs1)
  print (T.uncons bs1)
  print (T.null bs1)
  print (T.null (pack ""))
  print (pack "\xD800") -- low surrogate
  print (pack "\xDFFF") -- high surrogate

  -- Data.Text.Encoding
  print $ decodeLatin1 "äöüß"

  let text = "øßΞóïűæいהłДป็ş" :: Text
  print $ encodeUtf8 text
  print $ encodeUtf16LE text
  print $ encodeUtf16BE text
  print $ encodeUtf32LE text
  print $ encodeUtf32BE text
  print $ decodeUtf8 (encodeUtf8 text) == text
  print $ decodeUtf16LE (encodeUtf16LE text) == text
  print $ decodeUtf16BE (encodeUtf16BE text) == text
  print $ decodeUtf32LE (encodeUtf32LE text) == text
  print $ decodeUtf32BE (encodeUtf32BE text) == text
