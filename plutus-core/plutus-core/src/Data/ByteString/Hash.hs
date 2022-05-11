-- | Hash functions for lazy [[Data.ByteString.ByteString]]s
{-# LANGUAGE TypeApplications #-}
module Data.ByteString.Hash
    ( sha2_256
    , sha3_256
    , blake2b_256
    ) where

import Cardano.Crypto.Hash.Blake2b
import Cardano.Crypto.Hash.Class
import Cardano.Crypto.Hash.SHA256
import Cardano.Crypto.Hash.SHA3_256
import Data.ByteString qualified as BS
import Data.Proxy

-- | Hash a [[BSL.ByteString]] using the SHA-256 hash function.
sha2_256 :: BS.ByteString -> BS.ByteString
sha2_256 = digest (Proxy @SHA256)

-- | Hash a [[BSL.ByteString]] using the SHA3-256 hash function.
sha3_256 :: BS.ByteString -> BS.ByteString
sha3_256 = digest (Proxy @SHA3_256)

-- | Hash a [[BSL.ByteString]] using the Blake2B-256 hash function.
blake2b_256 :: BS.ByteString -> BS.ByteString
blake2b_256 = digest (Proxy @Blake2b_256)
