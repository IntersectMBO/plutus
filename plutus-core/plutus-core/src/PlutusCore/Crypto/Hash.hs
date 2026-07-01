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
{- C-free build (see Note [The with-crypto flag] in PlutusCore.Crypto.Utils).
Unlike the signature and BLS12-381 primitives, the hashes are needed at COMPILE
time (e.g. PlutusLedgerApi computes script hashes with blake2b_224), so they
cannot be stubbed. They are all standard algorithms, so we compute them with
@crypton@, which vendors its C sources and declares no @pkgconfig-depends@ (so
it needs no system C library) and produces byte-identical output. -}
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

sha2_256, sha3_256, blake2b_224, blake2b_256, keccak_256, ripemd_160
  :: BS.ByteString -> BS.ByteString

#ifdef WITH_CRYPTO

-- cardano-crypto-class (libsodium-backed) implementations.
sha2_256 = digest (Proxy @SHA256)
sha3_256 = digest (Proxy @SHA3_256)
blake2b_224 = digest (Proxy @Blake2b_224)
blake2b_256 = digest (Proxy @Blake2b_256)
keccak_256 = digest (Proxy @Keccak256)
ripemd_160 = digest (Proxy @RIPEMD160)

#else

-- crypton (vendored C, no system library) implementations.
sha2_256 = BA.convert . hashWith SHA256
sha3_256 = BA.convert . hashWith SHA3_256
blake2b_224 = BA.convert . hashWith Blake2b_224
blake2b_256 = BA.convert . hashWith Blake2b_256
keccak_256 = BA.convert . hashWith Keccak_256
ripemd_160 = BA.convert . hashWith RIPEMD160

#endif
