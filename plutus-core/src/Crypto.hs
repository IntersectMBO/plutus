module Crypto (verifySignature) where

import           Control.Applicative
import           Crypto.ECC.Ed25519Donna
import           Crypto.Error            (maybeCryptoError)
import qualified Data.ByteString         as BS

verifySignature
    :: Alternative f
    => BS.ByteString  -- ^ Public Key
    -> BS.ByteString  -- ^ Message
    -> BS.ByteString  -- ^ Signature
    -> f Bool
verifySignature pubKey msg sig =
    maybe empty pure . maybeCryptoError $
        verify
            <$> publicKey pubKey
            <*> pure msg
            <*> signature sig
