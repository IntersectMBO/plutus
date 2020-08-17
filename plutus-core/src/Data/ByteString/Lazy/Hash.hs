-- | Hash functions for lazy [[Data.ByteString.Lazy.ByteString]]s
{-# LANGUAGE TypeApplications #-}
module Data.ByteString.Lazy.Hash
    ( sha2
    , sha3
    ) where

import           Crypto.Hash          (SHA256, SHA3_256, hashlazy)
import qualified Data.ByteArray       as B
import qualified Data.ByteString.Lazy as BSL

-- | Hash a [[BSL.ByteString]] using the SHA-256 hash function.
sha2 :: BSL.ByteString -> BSL.ByteString
sha2 = BSL.fromStrict . B.convert . hashlazy @SHA256

-- | Hash a [[BSL.ByteString]] using the SHA3-256 hash function.
sha3 :: BSL.ByteString -> BSL.ByteString
sha3 = BSL.fromStrict . B.convert . hashlazy @SHA3_256
