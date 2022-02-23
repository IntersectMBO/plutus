{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}

module Crypto (
  verifySignature,
  verifySECP256k1Signature
  ) where

import Cardano.Crypto.DSIGN.Class qualified as DSIGN
import Cardano.Crypto.DSIGN.EcdsaSecp256k1 (EcdsaSecp256k1DSIGN)
import Control.Applicative
import Crypto.ECC.Ed25519Donna
import Crypto.Error (maybeCryptoError)
import Crypto.Secp256k1 qualified as SECP
import Data.ByteString qualified as BS
import PlutusCore.Builtin.Emitter (Emitter, emitM)
import PlutusCore.Evaluation.Result (EvaluationResult (EvaluationFailure))

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

verifySECP256k1Signature
  :: BS.ByteString -- ^ Public key
  -> BS.ByteString -- ^ Signature
  -> BS.ByteString -- ^ Message hash
  -> Emitter (EvaluationResult Bool)
verifySECP256k1Signature pk sig msg =
  case DSIGN.rawDeserialiseVerKeyDSIGN @EcdsaSecp256k1DSIGN pk of
    Nothing -> do
      emitM "SECP256k1: Given invalid signing key."
      pure EvaluationFailure
    Just pk' -> case DSIGN.rawDeserialiseSigDSIGN @EcdsaSecp256k1DSIGN sig of
      Nothing -> do
        emitM "SECP256k1: Given invalid signature."
        pure EvaluationFailure
      Just sig' -> case SECP.msg msg of
        Nothing -> do
          emitM "SECP256k1: Given invalid message hash."
          pure EvaluationFailure
        Just msg' -> case DSIGN.verifyDSIGN () pk' msg' sig' of
          Left _   -> pure . pure $ False
          Right () -> pure . pure $ True
