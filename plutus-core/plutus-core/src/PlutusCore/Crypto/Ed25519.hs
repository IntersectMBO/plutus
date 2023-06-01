{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}

module PlutusCore.Crypto.Ed25519 (
   verifyEd25519Signature_V1,
   verifyEd25519Signature_V2
   ) where

import PlutusCore.Crypto.Utils

import Cardano.Crypto.DSIGN.Class qualified as DSIGN
import Cardano.Crypto.DSIGN.Ed25519 (Ed25519DSIGN)
import Crypto.ECC.Ed25519Donna (publicKey, signature, verify)
import Crypto.Error (CryptoFailable (..))
import Data.ByteString qualified as BS
import Data.Text (Text, pack)
import PlutusCore.Builtin.Emitter (Emitter)
import PlutusCore.Evaluation.Result (EvaluationResult)

-- | Ed25519 signature verification
-- This will fail if the key or the signature are not of the expected length.
-- This version uses the cardano-crypto implementation of the verification function.
verifyEd25519Signature_V1
    :: BS.ByteString  -- ^ Public Key (32 bytes)
    -> BS.ByteString  -- ^ Message    (arbitrary length)
    -> BS.ByteString  -- ^ Signature  (64 bytes)
    -> Emitter (EvaluationResult Bool)
verifyEd25519Signature_V1 pubKey msg sig =
    case verify
             <$> publicKey pubKey
             <*> pure msg
             <*> signature sig
    of CryptoPassed r   -> pure $ pure r
       CryptoFailed err -> failWithMessage loc $ pack (show err)
  where
    loc :: Text
    loc = "Ed25519 signature verification"

-- | Ed25519 signature verification
-- This will fail if the key or the signature are not of the expected length.
-- This version uses the cardano-crypto-class implementation of the verification
-- function (using libsodium).
verifyEd25519Signature_V2
    :: BS.ByteString  -- ^ Public Key (32 bytes)
    -> BS.ByteString  -- ^ Message    (arbitrary length)
    -> BS.ByteString  -- ^ Signature  (64 bytes)
    -> Emitter (EvaluationResult Bool)
verifyEd25519Signature_V2 pk msg sig =
  case DSIGN.rawDeserialiseVerKeyDSIGN @Ed25519DSIGN pk of
    Nothing -> failWithMessage loc "Invalid verification key."
    Just pk' -> case DSIGN.rawDeserialiseSigDSIGN @Ed25519DSIGN sig of
      Nothing -> failWithMessage loc "Invalid signature."
      Just sig' ->
          pure . pure $
               case DSIGN.verifyDSIGN () pk' msg sig' of
                 Left _   -> False
                 Right () -> True
  where
    loc :: Text
    loc = "Ed25519 signature verification"

