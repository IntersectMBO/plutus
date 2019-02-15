module Crypto (verifySignature) where

import           Crypto.ECC.Ed25519Donna
import           Crypto.Error            (maybeCryptoError)
import qualified Data.ByteString.Lazy    as BSL
import           PlutusPrelude

verifySignature :: BSL.ByteString -- ^ Public Key
                -> BSL.ByteString -- ^ Message
                -> BSL.ByteString -- ^ Signature
                -> Maybe Bool
verifySignature pubKey msg sig =
    maybeCryptoError (verify <$> publicKey (BSL.toStrict pubKey) <*> pure (BSL.toStrict msg) <*> signature (BSL.toStrict sig))
