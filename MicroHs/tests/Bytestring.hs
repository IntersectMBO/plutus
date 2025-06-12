module Bytestring where
import Data.ByteString as BS
import Data.Word

bs1 :: ByteString
bs1 = pack [1,2,3]

bs2 :: ByteString
bs2 = pack [1,2,4]

bs3 :: ByteString
bs3 = pack [1,2]

bs4 :: ByteString
bs4 = pack [1,3,4]

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
  print $ unpack "abc"
  print $ BS.replicate 64 42

  -- breakSubstring
  print $ breakSubstring "def" "abcdefg"
  print $ breakSubstring "abc" "abcdefg"
  print $ breakSubstring "fg" "abcdefg"
  print $ breakSubstring "fn" "abcdefg"

  -- isValidUtf8
  print $ isValidUtf8 "\xC1\xB9"
  print $ isValidUtf8 "\xE0\x8E\xA9"
  print $ isValidUtf8 "\xF0\x80\x8E\xA9"
  print $ isValidUtf8 "\xF4\x90\x80\x80"
  print $ isValidUtf8 "\xED\xA0\x80" -- low surrogate
  print $ isValidUtf8 "\xED\xBF\xBF" -- high surrogate

  -- ByteString literals
  print ("øßΞóïűæいהłДป็ş" :: ByteString)
