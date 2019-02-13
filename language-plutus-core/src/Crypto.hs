module Crypto (verifySignature) where

import           Crypto.ECC.Ed25519Donna
import           Crypto.Error            (maybeCryptoError)
import qualified Data.ByteString.Lazy    as BSL
import           PlutusPrelude

-- This should return (error bool) when it fails (and the spec should be updated
-- to reflect this); this code will be changed
verifySignature :: BSL.ByteString -- ^ Public Key
                -> BSL.ByteString -- ^ Message
                -> BSL.ByteString -- ^ Signature
                -> Bool
verifySignature pubKey msg sig = fromMaybe False $
    maybeCryptoError (verify <$> publicKey (BSL.toStrict pubKey) <*> pure (BSL.toStrict msg) <*> signature (BSL.toStrict sig))
