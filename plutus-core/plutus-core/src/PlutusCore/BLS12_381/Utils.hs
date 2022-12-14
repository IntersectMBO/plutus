module PlutusCore.BLS12_381.Utils (toHexString)
where

import Data.ByteString (ByteString, foldr')
import Text.Printf (printf)

toHexString :: ByteString -> String
toHexString bs = "0x" ++ (Prelude.concat $ foldr' (\w s -> (printf "%02x" w):s) [] bs)

