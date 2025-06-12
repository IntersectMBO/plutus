module ByteStringIO where

import Data.ByteString as BS hiding (map)
import Data.Char
import System.IO (stdout)

text :: ByteString
text = BS.pack $ map (fromIntegral . ord) "Lorem ipsum dolor sit amet, consectetur adipiscing elit, sed do eiusmod tempor incididunt ut labore et dolore magna aliqua. Ut enim ad minim veniam, quis nostrud exercitation ullamco laboris nisi ut aliquip ex ea commodo consequat. Duis aute irure dolor in reprehenderit in voluptate velit esse cillum dolore eu fugiat nulla pariatur. Excepteur sint occaecat cupidatat non proident, sunt in culpa qui officia deserunt mollit anim id est laborum."

main :: IO ()
main = do
  BS.writeFile "test.tmp" text
  bs <- BS.readFile "test.tmp"
  print $ bs == text
  BS.hPut stdout (BS.pack [72, 101, 108, 108, 111, 33, 10]) -- "Hello!\n"
