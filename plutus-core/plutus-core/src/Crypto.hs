module Crypto (verifySignature) where

import Control.Applicative
import Crypto.ECC.Ed25519Donna
import Crypto.Error (maybeCryptoError)
import Data.ByteString qualified as BS

-- Ed25519 signature verification
-- This will fail if the key or the signature are not of the expected length.
verifySignature
    :: Alternative f
    => BS.ByteString  -- ^ Public Key (32 bytes)
    -> BS.ByteString  -- ^ Message    (arbirtary length)
    -> BS.ByteString  -- ^ Signature  (64 bytes)
    -> f Bool
verifySignature pubKey msg sig =
    maybe empty pure . maybeCryptoError $
        verify
            <$> publicKey pubKey
            <*> pure msg
            <*> signature sig
