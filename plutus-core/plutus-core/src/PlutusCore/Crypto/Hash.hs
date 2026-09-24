{-# LANGUAGE CPP #-}
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

import Data.ByteString qualified as BS

#ifdef WITH_CRYPTO
import Cardano.Crypto.Hash.Blake2b
import Cardano.Crypto.Hash.Class
import Cardano.Crypto.Hash.Keccak256
import Cardano.Crypto.Hash.RIPEMD160
import Cardano.Crypto.Hash.SHA256
import Cardano.Crypto.Hash.SHA3_256
import Data.Proxy
#else
import Crypto.Hash (hashWith)
import Crypto.Hash.Algorithms
  ( Blake2b_224 (..)
  , Blake2b_256 (..)
  , Keccak_256 (..)
  , RIPEMD160 (..)
  , SHA256 (..)
  , SHA3_256 (..)
  )
import Data.ByteArray qualified as BA
#endif

-- | Hash a `ByteString` using the SHA-256 hash function.
sha2_256 :: BS.ByteString -> BS.ByteString

-- | Hash a `ByteString` using the SHA3-256 hash function.
sha3_256 :: BS.ByteString -> BS.ByteString

-- | Hash a `ByteString` using the Blake2b-224 hash function.
blake2b_224 :: BS.ByteString -> BS.ByteString

-- | Hash a `ByteString` using the Blake2b-256 hash function.
blake2b_256 :: BS.ByteString -> BS.ByteString

-- | Hash a `ByteString` using the Keccak-256 hash function.
keccak_256 :: BS.ByteString -> BS.ByteString

-- | Hash a `ByteString` using the RIPEMD-160 hash function.
ripemd_160 :: BS.ByteString -> BS.ByteString

#ifdef WITH_CRYPTO

sha2_256 = digest (Proxy @SHA256)
sha3_256 = digest (Proxy @SHA3_256)
blake2b_224 = digest (Proxy @Blake2b_224)
blake2b_256 = digest (Proxy @Blake2b_256)
keccak_256 = digest (Proxy @Keccak256)
ripemd_160 = digest (Proxy @RIPEMD160)

#else

sha2_256 = BA.convert . hashWith SHA256
sha3_256 = BA.convert . hashWith SHA3_256
blake2b_224 = BA.convert . hashWith Blake2b_224
blake2b_256 = BA.convert . hashWith Blake2b_256
keccak_256 = BA.convert . hashWith Keccak_256
ripemd_160 = BA.convert . hashWith RIPEMD160

#endif
