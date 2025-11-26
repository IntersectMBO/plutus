{-# LANGUAGE TypeApplications #-}

-- | Hash functions for lazy [[Data.ByteString.ByteString]]s
module PlutusCore.Crypto.Hash
  ( sha2_256
  , sha3_256
  , blake2b_224
  , blake2b_256
  , keccak_256
  , ripemd_160
  ) where

import Cardano.Crypto.Hash.Blake2b
import Cardano.Crypto.Hash.Class
import Cardano.Crypto.Hash.Keccak256
import Cardano.Crypto.Hash.RIPEMD160
import Cardano.Crypto.Hash.SHA256
import Cardano.Crypto.Hash.SHA3_256
import Data.ByteString qualified as BS
import Data.Proxy

-- | Hash a `ByteString` using the SHA-256 hash function.
sha2_256 :: BS.ByteString -> BS.ByteString
sha2_256 = digest (Proxy @SHA256)

-- | Hash a `ByteString` using the SHA3-256 hash function.
sha3_256 :: BS.ByteString -> BS.ByteString
sha3_256 = digest (Proxy @SHA3_256)

-- | Hash a `ByteString` using the Blake2b-224 hash function.
blake2b_224 :: BS.ByteString -> BS.ByteString
blake2b_224 = digest (Proxy @Blake2b_224)

-- | Hash a `ByteString` using the Blake2b-256 hash function.
blake2b_256 :: BS.ByteString -> BS.ByteString
blake2b_256 = digest (Proxy @Blake2b_256)

-- | Hash a `ByteString` using the Keccak-256 hash function.
keccak_256 :: BS.ByteString -> BS.ByteString
keccak_256 = digest (Proxy @Keccak256)

-- | Hash a `ByteString` using the RIPEMD-160 hash function.
ripemd_160 :: BS.ByteString -> BS.ByteString
ripemd_160 = digest (Proxy @RIPEMD160)
