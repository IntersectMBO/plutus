{-# LANGUAGE TypeFamilies #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

{-|
This module re-exports the module 'Plutus.V1.Ledger.Scripts', but with
additionnal functionality.

This module contains orphan instances of 'Cardano.Api.HasTextEnvelope', since
the Cardano Node CLI expects serialised binary values to be wrapped with a
'Cardano.Api.TextEnvelope'.
-}
module Ledger.Scripts (
  module Export
  ) where

import           Cardano.Api              (AsType, HasTextEnvelope (textEnvelopeType), HasTypeProxy (proxyToAsType),
                                           SerialiseAsCBOR, TextEnvelopeType (TextEnvelopeType))
import           Cardano.Binary           (FromCBOR (fromCBOR), ToCBOR (toCBOR))
import           Codec.Serialise          (decode, encode)
import qualified Data.Text                as Text
import           Plutus.V1.Ledger.Api     (plutusScriptEnvelopeType)
import           Plutus.V1.Ledger.Scripts as Export

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
