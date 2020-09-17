-- | Hash functions for lazy [[Data.ByteString.ByteString]]s
{-# LANGUAGE TypeApplications #-}
module Data.ByteString.Hash
    ( sha2
    , sha3
    ) where

import           Crypto.Hash     (SHA256, SHA3_256, hash)
import qualified Data.ByteArray  as B
import qualified Data.ByteString as BS

-- | Hash a [[BSL.ByteString]] using the SHA-256 hash function.
sha2 :: BS.ByteString -> BS.ByteString
sha2 = B.convert . hash @BS.ByteString @SHA256

-- | Hash a [[BSL.ByteString]] using the SHA3-256 hash function.
sha3 :: BS.ByteString -> BS.ByteString
sha3 = B.convert . hash @BS.ByteString @SHA3_256
