{-# LANGUAGE KindSignatures    #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}

module Crypto (
  verifyEd25519Signature,
  verifyEcdsaSecp256k1Signature,
  verifySchnorrSecp256k1Signature,
  ) where

import Cardano.Crypto.DSIGN.Class qualified as DSIGN
import Cardano.Crypto.DSIGN.EcdsaSecp256k1 (EcdsaSecp256k1DSIGN, toMessageHash)
import Cardano.Crypto.DSIGN.SchnorrSecp256k1 (SchnorrSecp256k1DSIGN)
import Control.Applicative (Alternative (empty))
import Crypto.ECC.Ed25519Donna (publicKey, signature, verify)
import Crypto.Error (maybeCryptoError)
import Data.ByteString qualified as BS
import Data.Kind (Type)
import Data.Text (Text)
import PlutusCore.Builtin.Emitter (Emitter, emit)
import PlutusCore.Evaluation.Result (EvaluationResult (EvaluationFailure))

-- | Ed25519 signature verification
-- This will fail if the key or the signature are not of the expected length.
verifyEd25519Signature
    :: Alternative f
    => BS.ByteString  -- ^ Public Key (32 bytes)
    -> BS.ByteString  -- ^ Message    (arbitrary length)
    -> BS.ByteString  -- ^ Signature  (64 bytes)
    -> f Bool
verifyEd25519Signature pubKey msg sig =
    maybe empty pure . maybeCryptoError $
        verify
            <$> publicKey pubKey
            <*> pure msg
            <*> signature sig

-- | Verify an ECDSA signature made using the SECP256k1 curve.
--
-- = Note
--
-- This takes a message /hash/, rather than a general blob of bytes; thus, it is
-- limited in length.
verifyEcdsaSecp256k1Signature
  :: BS.ByteString -- ^ Public key   (64 bytes)
  -> BS.ByteString -- ^ Message hash (32 bytes)
  -> BS.ByteString -- ^ Signature    (64 bytes)
  -> Emitter (EvaluationResult Bool)
verifyEcdsaSecp256k1Signature pk msg sig =
  case DSIGN.rawDeserialiseVerKeyDSIGN @EcdsaSecp256k1DSIGN pk of
    Nothing -> failWithMessage loc "Invalid verification key."
    Just pk' -> case DSIGN.rawDeserialiseSigDSIGN @EcdsaSecp256k1DSIGN sig of
      Nothing -> failWithMessage loc "Invalid signature."
      Just sig' -> case toMessageHash msg of
        Nothing -> failWithMessage loc "Invalid message hash."
        Just msg' -> pure . pure $ case DSIGN.verifyDSIGN () pk' msg' sig' of
          Left _   -> False
          Right () -> True
  where
    loc :: Text
    loc = "ECDSA SECP256k1 signature verification"

-- | Verify a Schnorr signature made using the SECP256k1 curve.
--
-- = Note
--
-- Unlike 'verifyEcdsaSecp256k1Signature', this can accept messages of arbitrary
-- form and length.
verifySchnorrSecp256k1Signature
  :: BS.ByteString -- ^ Public key (64 bytes)
  -> BS.ByteString -- ^ Message    (arbitrary length)
  -> BS.ByteString -- ^ Signature  (64 bytes)
  -> Emitter (EvaluationResult Bool)
verifySchnorrSecp256k1Signature pk msg sig =
  case DSIGN.rawDeserialiseVerKeyDSIGN @SchnorrSecp256k1DSIGN pk of
    Nothing -> failWithMessage loc "Invalid verification key."
    Just pk' -> case DSIGN.rawDeserialiseSigDSIGN @SchnorrSecp256k1DSIGN sig of
      Nothing -> failWithMessage loc "Invalid signature."
      Just sig' -> pure . pure $ case DSIGN.verifyDSIGN () pk' msg sig' of
        Left _   -> False
        Right () -> True
  where
    loc :: Text
    loc = "Schnorr SECP256k1 signature verification"

-- Helpers

-- TODO: Something like 'failWithMessage x y *> foo' should really fail with
-- 'EvaluationFailure' without evaluating 'foo', but currently it will. This
-- requires a fix to how Emitter and EvaluationResult work, and since we don't
-- expect 'failWithMessage' to be used this way, we note this for future
-- reference only for when such fixes are made.
failWithMessage :: forall (a :: Type) .
  Text -> Text -> Emitter (EvaluationResult a)
failWithMessage location reason = do
  emit $ location <> ": " <> reason
  pure EvaluationFailure
