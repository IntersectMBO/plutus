{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}

module PlutusCore.Crypto.Ed25519 (verifyEd25519Signature)
where

import PlutusCore.Builtin.KnownType (BuiltinResult)
import PlutusCore.Crypto.Utils

import Cardano.Crypto.DSIGN.Class qualified as DSIGN
import Cardano.Crypto.DSIGN.Ed25519 (Ed25519DSIGN)
import Data.ByteString qualified as BS
import Data.Text (Text)

{-| Ed25519 signature verification
This will fail if the key or the signature are not of the expected length.
This version uses the cardano-crypto-class implementation of the verification
function (using libsodium). -}
verifyEd25519Signature
  :: BS.ByteString
  -- ^ Public Key (32 bytes)
  -> BS.ByteString
  -- ^ Message    (arbitrary length)
  -> BS.ByteString
  -- ^ Signature  (64 bytes)
  -> BuiltinResult Bool
verifyEd25519Signature pk msg sig =
  case DSIGN.rawDeserialiseVerKeyDSIGN @Ed25519DSIGN pk of
    Nothing -> failWithMessage loc "Invalid verification key."
    Just pk' -> case DSIGN.rawDeserialiseSigDSIGN @Ed25519DSIGN sig of
      Nothing -> failWithMessage loc "Invalid signature."
      Just sig' ->
        pure $
          case DSIGN.verifyDSIGN () pk' msg sig' of
            Left _ -> False
            Right () -> True
  where
    loc :: Text
    loc = "Ed25519 signature verification"
