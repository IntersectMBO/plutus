module PlutusCore.BLS12_381.Utils (byteStringAsHex)
where

import Data.ByteString (ByteString, foldr')
import Text.Printf (printf)

byteStringAsHex :: ByteString -> String
byteStringAsHex bs = "0x" ++ (Prelude.concat $ foldr' (\w s -> (printf "%02x" w):s) [] bs)

