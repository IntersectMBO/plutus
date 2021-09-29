{-# LANGUAGE TypeFamilies #-}

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
    , redeemerHash
    , validatorHash
    , mintingPolicyHash
    , stakeValidatorHash
    , toCardanoApiScript
    , scriptHash
    , dataHash
    ) where

import           Cardano.Api              (AsType, HasTextEnvelope (textEnvelopeType), HasTypeProxy (proxyToAsType),
                                           SerialiseAsCBOR, TextEnvelopeType (TextEnvelopeType))
import qualified Cardano.Api              as Script
import qualified Cardano.Api.Shelley      as Script
import           Cardano.Binary           (FromCBOR (fromCBOR), ToCBOR (toCBOR))
import           Codec.Serialise          (decode, encode, serialise)
import qualified Data.ByteString.Lazy     as BSL
import qualified Data.ByteString.Short    as SBS
import qualified Data.Text                as Text
import           Plutus.V1.Ledger.Api     (plutusDatumEnvelopeType, plutusRedeemerEnvelopeType,
                                           plutusScriptEnvelopeType)
import           Plutus.V1.Ledger.Scripts as Export
import           PlutusTx.Builtins        as Builtins

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
datumHash = DatumHash . dataHash . getDatum

redeemerHash :: Redeemer -> RedeemerHash
redeemerHash = RedeemerHash . dataHash . getRedeemer

validatorHash :: Validator -> ValidatorHash
validatorHash = ValidatorHash . getScriptHash . scriptHash . getValidator

mintingPolicyHash :: MintingPolicy -> MintingPolicyHash
mintingPolicyHash = MintingPolicyHash . getScriptHash . scriptHash . getMintingPolicy

stakeValidatorHash :: StakeValidator -> StakeValidatorHash
stakeValidatorHash = StakeValidatorHash . getScriptHash . scriptHash . getStakeValidator

-- | Hash a 'Builtins.BuiltinData'
dataHash :: Builtins.BuiltinData -> Builtins.BuiltinByteString
dataHash =
    toBuiltin
    . Script.serialiseToRawBytes
    . Script.hashScriptData
    . Script.fromPlutusData
    . builtinDataToData

-- | Hash a 'Script'
scriptHash :: Script -> ScriptHash
scriptHash =
    ScriptHash
    . toBuiltin
    . Script.serialiseToRawBytes
    . Script.hashScript
    . toCardanoApiScript

-- | Convert a 'Script' to a 'cardano-api' script
toCardanoApiScript :: Script -> Script.Script Script.PlutusScriptV1
toCardanoApiScript =
    Script.PlutusScript Script.PlutusScriptV1
    . Script.PlutusScriptSerialised
    . SBS.toShort
    . BSL.toStrict
    . serialise
