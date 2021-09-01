{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies     #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

{-|
This module re-exports the module 'Plutus.V1.Ledger.Scripts', but with
additional functionality.

This module contains orphan instances of 'Cardano.Api.HasTextEnvelope', since
the Cardano Node CLI expects serialised binary values to be wrapped with a
'Cardano.Api.TextEnvelope'.
-}
module Ledger.Scripts (
    module Export
    , datumHash
    , datumInputsAt
    , datumOutputsAt
    , toDatumHash
    , toRedeemer
    , fromRedeemer
    , redeemerHash
    , validatorHash
    , mintingPolicyHash
    , stakeValidatorHash
    ) where

import           Cardano.Api               (AsType, HasTextEnvelope (textEnvelopeType), HasTypeProxy (proxyToAsType),
                                            SerialiseAsCBOR, TextEnvelopeType (TextEnvelopeType))
import           Cardano.Binary            (FromCBOR (fromCBOR), ToCBOR (toCBOR))
import qualified Cardano.Crypto.Hash       as Crypto
import           Codec.Serialise           (Serialise, decode, encode, serialise)
import qualified Data.ByteArray            as BA
import qualified Data.ByteString.Lazy      as BSL
import qualified Data.Text                 as Text
import           Plutus.V1.Ledger.Api      (FromData, TxInfo, Value, plutusDatumEnvelopeType,
                                            plutusRedeemerEnvelopeType, plutusScriptEnvelopeType)
import qualified Plutus.V1.Ledger.Api      as Ledger
import qualified Plutus.V1.Ledger.Api      as PlutusTx
import           Plutus.V1.Ledger.Contexts (findDatum, scriptInputsAt, scriptOutputsAt)
import           Plutus.V1.Ledger.Scripts  as Export
import           PlutusTx.Builtins         as Builtins
import qualified PlutusTx.Foldable         as Foldable

instance HasTextEnvelope Script where
    textEnvelopeType _ = TextEnvelopeType $ Text.unpack plutusScriptEnvelopeType

instance SerialiseAsCBOR Script

instance FromCBOR Script where
    fromCBOR = decode

instance ToCBOR Script where
    toCBOR = encode

instance HasTypeProxy Script where
    data AsType Script = AsScript
    proxyToAsType _ = AsScript

instance HasTextEnvelope Datum where
  textEnvelopeType _ = TextEnvelopeType $ Text.unpack plutusDatumEnvelopeType

instance SerialiseAsCBOR Datum

instance FromCBOR Datum where
    fromCBOR = decode

instance ToCBOR Datum where
    toCBOR = encode

instance HasTypeProxy Datum where
    data AsType Datum = AsDatum
    proxyToAsType _ = AsDatum

instance HasTextEnvelope Redeemer where
  textEnvelopeType _ = TextEnvelopeType $ Text.unpack plutusRedeemerEnvelopeType

instance SerialiseAsCBOR Redeemer

instance FromCBOR Redeemer where
    fromCBOR = decode

instance ToCBOR Redeemer where
    toCBOR = encode

instance HasTypeProxy Redeemer where
    data AsType Redeemer = AsRedeemer
    proxyToAsType _ = AsRedeemer

datumHash :: Datum -> DatumHash
datumHash = Ledger.DatumHash . Builtins.sha2_256 . BA.convert

-- | Get 'DatumHash' using 'ToData' instance.
-- **Note**: not intended to be used on-chain.
toDatumHash
  :: forall datum.
     Ledger.ToData datum
  => datum
  -> Ledger.DatumHash
toDatumHash = datumHash . toDatum @datum


{-# INLINEABLE datumOutputsAt #-}

-- | Version of scriptOutputsAt which also extracts the associated Datums
datumOutputsAt
  :: forall datum.
     FromData datum
  => ValidatorHash
  -> TxInfo
  -> [(datum, Value)]
datumOutputsAt script txInfo = do
  (datumHash, value) <- scriptOutputsAt script txInfo
  datum <-
    Foldable.toList $
      findDatum datumHash txInfo >>= (fromDatum @datum)
  [(datum, value)] -- PlutusTx doesn't export Applicative List, for some reason

{-# INLINEABLE datumInputsAt #-}

-- | Version scriptInputsAt which also extracts the associated Datums
datumInputsAt
  :: forall datum.
     PlutusTx.FromData datum
  => ValidatorHash
  -> TxInfo
  -> [(datum, Ledger.Value)]
datumInputsAt script txInfo = do
  (datumHash, value) <- scriptInputsAt script txInfo
  datum <-
    Foldable.toList $
      findDatum datumHash txInfo >>= fromDatum @datum
  [(datum, value)]

-- | Construct 'Redeemer' using 'ToData' instance.
{-# INLINEABLE toRedeemer #-}
toRedeemer :: Ledger.ToData redeemer => redeemer -> Ledger.Redeemer
toRedeemer = Ledger.Redeemer . Ledger.toBuiltinData

-- | Parse 'Redeemer' using 'FromData' instance.
{-# INLINEABLE fromRedeemer #-}
fromRedeemer :: Ledger.FromData redeemer => Ledger.Redeemer -> Maybe redeemer
fromRedeemer (Ledger.Redeemer d) = Ledger.fromBuiltinData d

redeemerHash :: Redeemer -> RedeemerHash
redeemerHash = RedeemerHash . Builtins.sha2_256 . BA.convert

validatorHash :: Validator -> ValidatorHash
validatorHash = ValidatorHash . scriptHash

mintingPolicyHash :: MintingPolicy -> MintingPolicyHash
mintingPolicyHash = MintingPolicyHash . scriptHash

stakeValidatorHash :: StakeValidator -> StakeValidatorHash
stakeValidatorHash = StakeValidatorHash . scriptHash

scriptHash :: Serialise a => a -> Builtins.BuiltinByteString
scriptHash =
    toBuiltin
    . Crypto.hashToBytes
    . Crypto.hashWith @Crypto.Blake2b_224 id
    . Crypto.hashToBytes
    . Crypto.hashWith @Crypto.Blake2b_224 id
    . BSL.toStrict
    . serialise
