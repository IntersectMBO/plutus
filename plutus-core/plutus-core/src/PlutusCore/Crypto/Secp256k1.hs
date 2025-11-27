{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}

module PlutusCore.Crypto.Secp256k1
  ( verifyEcdsaSecp256k1Signature
  , verifySchnorrSecp256k1Signature
  ) where

import PlutusCore.Builtin.Result
import PlutusCore.Crypto.Utils

import Cardano.Crypto.DSIGN.Class qualified as DSIGN
import Cardano.Crypto.DSIGN.EcdsaSecp256k1 (EcdsaSecp256k1DSIGN, toMessageHash)
import Cardano.Crypto.DSIGN.SchnorrSecp256k1 (SchnorrSecp256k1DSIGN)
import Data.ByteString qualified as BS
import Data.Text (Text)

{-| Verify an ECDSA signature made using the SECP256k1 curve.

= Note

There are additional well-formation requirements for the arguments beyond
their length:

* The first byte of the public key must correspond to the sign of the /y/
coordinate: this is @0x02@ if /y/ is even, and @0x03@ otherwise.
* The remaining bytes of the public key must correspond to the /x/
coordinate, as a big-endian integer.
* The first 32 bytes of the signature must correspond to the big-endian
integer representation of _r_.
* The last 32 bytes of the signature must correspond to the big-endian
integer representation of _s_.

While this primitive /accepts/ a hash, any caller should only pass it hashes
that they computed themselves: specifically, they should receive the
/message/ from a sender and hash it, rather than receiving the /hash/ from
said sender. Failure to do so can be
[dangerous](https://bitcoin.stackexchange.com/a/81116/35586). Other than
length, we make no requirements of what hash gets used. -}
verifyEcdsaSecp256k1Signature
  :: BS.ByteString
  -- ^ Public key   (33 bytes)
  -> BS.ByteString
  -- ^ Message hash (32 bytes)
  -> BS.ByteString
  -- ^ Signature    (64 bytes)
  -> BuiltinResult Bool
verifyEcdsaSecp256k1Signature pk msg sig =
  case DSIGN.rawDeserialiseVerKeyDSIGN @EcdsaSecp256k1DSIGN pk of
    Nothing -> failWithMessage loc "Invalid verification key."
    Just pk' -> case DSIGN.rawDeserialiseSigDSIGN @EcdsaSecp256k1DSIGN sig of
      Nothing -> failWithMessage loc "Invalid signature."
      Just sig' -> case toMessageHash msg of
        Nothing -> failWithMessage loc "Invalid message hash."
        Just msg' -> pure $ case DSIGN.verifyDSIGN () pk' msg' sig' of
          Left _ -> False
          Right () -> True
  where
    loc :: Text
    loc = "ECDSA SECP256k1 signature verification"

{-| Verify a Schnorr signature made using the SECP256k1 curve.

= Note

There are additional well-formation requirements for the arguments beyond
their length. Throughout, we refer to co-ordinates of the point @R@.

* The bytes of the public key must correspond to the /x/ coordinate, as a
big-endian integer, as specified in BIP-340.
* The first 32 bytes of the signature must correspond to the /x/ coordinate,
as a big-endian integer, as specified in BIP-340.
* The last 32 bytes of the signature must correspond to the bytes of /s/, as
a big-endian integer, as specified in BIP-340.

= See also

* [BIP-340](https://github.com/bitcoin/bips/blob/master/bip-0340.mediawiki) -}
verifySchnorrSecp256k1Signature
  :: BS.ByteString
  -- ^ Public key (32 bytes)
  -> BS.ByteString
  -- ^ Message    (arbitrary length)
  -> BS.ByteString
  -- ^ Signature  (64 bytes)
  -> BuiltinResult Bool
verifySchnorrSecp256k1Signature pk msg sig =
  case DSIGN.rawDeserialiseVerKeyDSIGN @SchnorrSecp256k1DSIGN pk of
    Nothing -> failWithMessage loc "Invalid verification key."
    Just pk' -> case DSIGN.rawDeserialiseSigDSIGN @SchnorrSecp256k1DSIGN sig of
      Nothing -> failWithMessage loc "Invalid signature."
      Just sig' -> pure $ case DSIGN.verifyDSIGN () pk' msg sig' of
        Left _ -> False
        Right () -> True
  where
    loc :: Text
    loc = "Schnorr SECP256k1 signature verification"
